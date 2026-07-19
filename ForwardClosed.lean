import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Object properties closed under forward morphisms

This file isolates a small reusable interface suggested by categorical proof
pipelines.  The predicate itself is Mathlib's `ObjectProperty`; the additional
structure records only the essential compatibility with morphisms.
-/

universe v v' u u'

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C]

/-- An object property is forward closed when every morphism transports it. -/
structure IsForwardClosed (P : ObjectProperty C) : Prop where
  map {X Y : C} (f : X ⟶ Y) : P X → P Y

namespace IsForwardClosed

variable {P Q : ObjectProperty C}

/-- A forward-closed property transports across an isomorphism in both directions. -/
theorem iso_iff (hP : IsForwardClosed P) {X Y : C} (e : X ≅ Y) : P X ↔ P Y := by
  exact ⟨hP.map e.hom, hP.map e.inv⟩

/-- The conjunction of two forward-closed properties is forward closed. -/
def and (hP : IsForwardClosed P) (hQ : IsForwardClosed Q) :
    IsForwardClosed (fun X ↦ P X ∧ Q X) where
  map f h := ⟨hP.map f h.1, hQ.map f h.2⟩

/-- The property holding of every object is forward closed. -/
def top : IsForwardClosed (⊤ : ObjectProperty C) where
  map _ _ := trivial

variable {D : Type u'} [Category.{v'} D]

/-- Forward closure pulls back along a functor. -/
def inverseImage (hP : IsForwardClosed P) (F : D ⥤ C) :
    IsForwardClosed (P.inverseImage F) where
  map f := hP.map (F.map f)

@[simp]
theorem inverseImage_comp (hP : IsForwardClosed P)
    {E : Type*} [Category E] (F : E ⥤ D) (G : D ⥤ C) :
    hP.inverseImage (F ⋙ G) = (hP.inverseImage G).inverseImage F := by
  rfl

/-- A natural transformation transports a pulled-back forward-closed property pointwise. -/
theorem naturalTransformation (hP : IsForwardClosed P) {F G : D ⥤ C}
    (α : F ⟶ G) (X : D) : P.inverseImage F X → P.inverseImage G X := by
  exact hP.map (α.app X)

/-- A terminal object is a canonical endpoint for every forward-closed property. -/
theorem terminal (hP : IsForwardClosed P) [HasTerminal C] {X : C} :
    P X → P (⊤_ C) := by
  exact hP.map (Limits.terminal.from X)

end IsForwardClosed
end CategoryTheory.ObjectProperty
