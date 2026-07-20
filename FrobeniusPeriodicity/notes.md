◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻  
*reference: copy pasted and edited from collaboration with computer agents  
not verified, non-machine checked, and maybe depends on basic axioms  
◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻◇◻  
>  


Yes. 
	
		 
		
			it removes irrelevant full periods
			
			 and selects the unique representative in [0,n).
			 
		Thus in

			F^m = F^(m % n), 
			
				the right side is the canonical mathematical normal form, 
				even though its syntax tree is larger.


	Because 
	
		(F^n=1), 
		
	writing 
		
		(m=qn+r) 
		
	gives 
		
		(F^m=(F^n)^qF^r=F^r). 
		
	The quotient 
	
		(q) 
		
	records irrelevant full cycles;
	
		(r=m\bmod n) 
		
	is the unique canonical exponent in 
	
		([0,n)).






		Exactly. 
		The hidden structure is a 
		
			**quotient + representative** 
				construction:

```
			ℕ  ──mod n──▶  ℕ/nℕ
			m = qn + r
			          r ∈ [0,n)
```

	The quotient `q` is “lost information” because:

```
F^(qn+r)
= (F^n)^q · F^r
= 1^q · F^r
= F^r
```

So:

```
F^m → F^(m%n)
```

		is a projection onto representatives.
		
		 The RHS is a larger syntax tree,
		  but a smaller **semantic space**:
		   many possible `m` collapse to one `r`. 🌱




		No: 
		
			the reverse direction has the opposite normalization behavior.
	
		Forward:
	
	```lean
			F ^ m = F ^ (m % n)
	```
	
		acts like a projection:
	
	```text
	17 → 2
	12 → 2
	7  → 2
	```
	
		Many terms collapse to one representative.
		
		Reverse:
			
			```lean
					F ^ (m % n) = F ^ m
				```
		
			tries to choose an `m` from:
		
		```text
			2 ← {2,7,12,17,...}
		```
	
		In Lean:
	
	```lean
	rw [reverse_theorem]
	```
	
			on
		
		```lean
		F ^ 2
		```
	
	must find `m` where:
	
	```lean
	m % n = 2
	```

		It may pick `m = 2` 
		
			(no visible change), 
			
				or another matching exponent depending on elaboration/context.

	As a 
	`[simp]` lemma, 
	
		it is problematic: 
		
			simp wants to move terms toward a stable normal form, but this rule moves canonical representatives back into the larger equivalence class. It can create larger terms and lose the bounded exponent invariant.

		So mathematically:
	
	```lean
	F^2 = F^17
	```
	
	is fine.
	
	Algorithmically:
	
	```lean
	normal form → arbitrary representative
	```
	
	is the wrong rewrite orientation. ∎






	A small refinement:
	
		 Lean’s `rw` does **not usually search for an arbitrary `m`**. The metavariable `m` comes from the theorem pattern, and matching is mostly syntactic. The danger appears more clearly with a simplifier/normalizer.

	Forward:
	
	```lean
	F ^ m = F ^ (m % n)
	```
	
	gives:
	
	```text
	F^17 → F^(17%5) → F^2
	F^12 → F^(12%5) → F^2
	```
	
	A terminating collapse:
	
	```text
	{F^2,F^7,F^12,F^17,...} → F^2
	```
	
	Reverse:
	
	```lean
	F ^ (m % n) = F ^ m
	```
	
	matches a term like:
	
	```text
	F^2
	```
	
	because `m := 2` works:
	
	```text
	F^(2%5) → F^2
	```
	
	but it does not inherently know “choose 17”. The real issue is orientation: it encourages leaving the chosen representative space. A good normalizer should have:
	
	```text
	equivalence class → chosen representative
	```
	
	not:
	
	```text
	representative → arbitrary member of class
	```
	
	So the quotient picture remains correct; only the Lean matching detail is subtler. 🌱



>
		Because every exponent splits into full cycles + remainder:
		
		```text
		m = qn + r
		```
		
		so:
		
		```text
		a^m = a^(qn+r)
		    = a^(qn)·a^r
		    = (a^n)^q·a^r
		```
		
		Given `a^n = 1`:
		
		```text
		(1)^q·a^r = a^r
		```
		
		The `qn` part contributes no change; only the remainder `r=m%n` matters. 🌱



	The theorem itself is excellent; the **orientation** is the key.

	```lean
	pow_eq_pow_mod :
	a ^ m = a ^ (m % n)
	```

	means:

	```text
	arbitrary exponent  →  canonical exponent
	```

	because:

	```text
	m = qn+r
	a^m = (a^n)^q a^r = 1^q a^r = a^r
	```

	The reverse:

	```lean
	a^(m%n) = a^m
	```

	is mathematically true, but it means:

	```text
	chosen representative → some member of the equivalence class
	```

	which is not a normalization rule.

	Analogy 🧭: 

		modulo classes are islands. 

			`m%n` is the harbor marker. The theorem says “sail to the harbor.” The reverse says “leave the harbor and pick any coastline point.” Both are valid navigation, but only one gives a canonical map.

	So `pow_eq_pow_mod` is exactly the right API orientation. ∎



	Yes. The key distinction is:

    Syntactic complexity:
	     m % n has a larger syntax tree than m.
    Semantic complexity: 
	    modulo periodicity, m % n is canonical and bounded.

	If F ^ n = 1 
	and m = qn + r
	 with 0 ≤ r < n,
	  then 
	  [ F^m=(F^n)^qF^r=F^r,\qquad r=m\bmod n. ] 
	  Thus q records irrelevant full cycles, 
	  while r is the unique representative in [0,n).

So

	F ^ m = F ^ (m % n)

	expresses a many-to-one normalization:

	17 ↘
	12 → 2
	 7 ↗

	The reverse equality is mathematically valid but conceptually points from a canonical representative toward an arbitrary exponent. Moreover, rewriting F ^ 2 with a universally quantified reverse theorem generally cannot infer an m by solving m % n = 2; rewriting does not perform that inverse search.

	Hence the forward orientation is appropriate for an explicit normalization theorem. Leaving it out of [simp] keeps modulo reduction deliberate and avoids unwanted global rewriting.




	Adding [simp] makes every simp call rewrite matching F^m terms automatically to F^(m % n). Although mathematically canonical, this can enlarge terms, introduce % unexpectedly, repeatedly alter goals, and require the period/cardinality witness to be inferred. Without [simp], normalization happens only when requested via rw, making proofs more predictable.







aᵐ → a⁽ᵐ mod n⁾

m = qn + r,  r = m mod n

aᵐ = a⁽qn+r⁾ = (aⁿ)q · aʳ = 1q · aʳ = aʳ

{m, m+n, m+2n, …} ⟶ r∈\[0,n)

∞ many reps  ──π──▶  ① canonical NF

reverse:
① NF ──↩──▶ ∞ reps  = expansion

`pow_eq_pow_mod` chooses collapse → normal form, not growth. 🌱


Dynamics chooses the reverse because the **goal of the rewrite is different**.

Group API:

[
a^m \rightarrow a^{m\bmod n}
]

means: “normalize the exponent”:

[
\text{large orbit point} \rightarrow \text{canonical representative}
]

Dynamics `[simp]` often wants:

[
f^{(m\bmod n)}(x) \rightarrow f^m(x)
]

because the modulo form is already a *specialized/derived expression* and simp wants to **remove extra structure**:

[
\text{short notation} \rightarrow \text{canonical computation form}
]

So:

* `pow_eq_pow_mod`: canonicalize **index** (m\mapsto m\bmod n)
* dynamics simp: canonicalize **term shape** by eliminating `%`

Different normal-form choices:

[
m \to m\bmod n
]

vs.

[
f^{m\bmod n}x \to f^mx
]

Both are valid; the API role decides the direction. 🌱