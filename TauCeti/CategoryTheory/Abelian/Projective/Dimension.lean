/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import TauCeti.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Comparing projective dimensions, and subobjects of projectives

If every bound `HasProjectiveDimensionLT X n` on one object implies the same bound on another
object `Y`, possibly in a different abelian category, then the projective dimension of `Y` is at
most that of `X`. This compares projective dimensions degree by degree without unfolding their
definition as an infimum.

In an abelian category with enough projectives, every object has projective dimension at most one
if and only if every subobject of a projective object is projective. This is the hereditary
condition, expressed using Mathlib's existing projective-dimension predicate.

When every object has projective dimension at most one, the criterion shows that the cycles and
boundaries of a complex of projective objects are projective. Surjections onto these boundaries
then split, so the cycles split off the terms.

When coproducts indexed by `ι` are exact, for instance for direct sums of modules, a coproduct of
objects of projective dimension at most `n` has projective dimension at most `n`
(`CategoryTheory.hasProjectiveDimensionLT_of_isColimit_cofan`). The index type is arbitrary, so
this also covers countable direct sums in a category of modules in any universe.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 4.2 (hereditary rings).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- If every bound on the projective dimension of `X` is also a bound for `Y`, then the projective
dimension of `Y` is at most that of `X`. The objects may lie in different abelian categories. -/
theorem projectiveDimension_le_of_hasProjectiveDimensionLT {D : Type*} [Category* D] [Abelian D]
    {X : C} {Y : D}
    (h : ∀ n : ℕ, HasProjectiveDimensionLT X n → HasProjectiveDimensionLT Y n) :
    projectiveDimension Y ≤ projectiveDimension X :=
  sInf_le_sInf fun _ hd i hi ↦ h i (hd i hi)

/-- A subobject of a projective object is projective if its quotient has projective dimension
at most one. -/
theorem projective_of_mono_of_hasProjectiveDimensionLE_one {X Y : C} (f : X ⟶ Y)
    [Mono f] [Projective Y] [HasProjectiveDimensionLE (cokernel f) 1] : Projective X := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
  exact projective_iff_hasProjectiveDimensionLT_one.mpr
    (hS.hasProjectiveDimensionLT_X₁ 1 inferInstance inferInstance)

variable (C) [EnoughProjectives C]

/-- Every object has projective dimension at most one precisely when every monomorphism into a
projective object has projective source. -/
theorem forall_hasProjectiveDimensionLE_one_iff_projective_of_mono :
    (∀ X : C, HasProjectiveDimensionLE X 1) ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [Mono f] [Projective Y], Projective X := by
  constructor
  · intro h X Y f _ _
    have := h (cokernel f)
    exact projective_of_mono_of_hasProjectiveDimensionLE_one f
  · intro h X
    obtain ⟨P⟩ := EnoughProjectives.presentation X
    have : Projective P.p := P.projective
    have : Epi P.f := P.epi
    have : Projective (kernel P.f) := h (kernel.ι P.f)
    have hS : (ShortComplex.mk (kernel.ι P.f) P.f (kernel.condition P.f)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel P.f) }
    exact hS.hasProjectiveDimensionLT_X₃ 1 inferInstance inferInstance

section Coproducts

variable {C} {ι : Type*} [HasColimitsOfShape (Discrete ι) C]
  [HasExactColimitsOfShape (Discrete ι) C]

/-- When coproducts indexed by `ι` are exact, the point of a colimit cofan of objects of
projective dimension `< n` has projective dimension `< n`. -/
theorem hasProjectiveDimensionLT_of_isColimit_cofan {X : ι → C} {c : Cofan X} (hc : IsColimit c)
    (n : ℕ) (h : ∀ i, HasProjectiveDimensionLT (X i) n) : HasProjectiveDimensionLT c.pt n := by
  induction n generalizing X c with
  | zero =>
    simp only [hasProjectiveDimensionLT_zero_iff_isZero] at h ⊢
    exact (IsZero.iff_id_eq_zero _).2 (Cofan.IsColimit.hom_ext hc _ _ fun i ↦ (h i).eq_of_src _ _)
  | succ n ih =>
    rcases n with _ | n
    · have (i : ι) : Projective (X i) := projective_iff_hasProjectiveDimensionLT_one.2 (h i)
      exact projective_iff_hasProjectiveDimensionLT_one.1 (Projective.of_isColimit_cofan hc)
    -- Cover every summand by a projective object; the kernels have projective dimension `< n + 1`.
    have hK (i : ι) : (ShortComplex.mk (kernel.ι (Projective.π (X i))) (Projective.π (X i))
        (kernel.condition _)).ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
    let T : ShortComplex (Discrete ι ⥤ C) :=
      ShortComplex.mk (X₁ := Discrete.functor fun i ↦ kernel (Projective.π (X i)))
        (X₂ := Discrete.functor fun i ↦ Projective.over (X i)) (X₃ := Discrete.functor X)
        (Discrete.natTrans fun i ↦ kernel.ι (Projective.π (X i.as)))
        (Discrete.natTrans fun i ↦ Projective.π (X i.as)) (by ext; simp)
    have hT : T.ShortExact := by
      have hP : JointlyReflectIsomorphisms fun i : Discrete ι ↦ (evaluation _ C).obj i :=
        ⟨fun f h ↦ have : ∀ i, IsIso (f.app i) := h; NatIso.isIso_of_isIso_app f⟩
      exact (hP.shortExact_iff T).2 fun i ↦ hK i.as
    -- Taking coproducts gives a short exact sequence `∐ ker ⟶ ∐ P ⟶ ∐ X`.
    have h₁ : HasProjectiveDimensionLT (colimit T.X₁) (n + 1) :=
      ih (colimit.isColimit _) fun i ↦ (hK i).hasProjectiveDimensionLT_X₁ (n + 1)
        (hasProjectiveDimensionLT_of_ge _ 1 _ (by lia)) (h i)
    have : Projective (colimit T.X₂) := Projective.of_isColimit_cofan (colimit.isColimit
      (Discrete.functor fun i ↦ Projective.over (X i)))
    have : HasProjectiveDimensionLT (colimit (Discrete.functor X)) (n + 2) :=
      (hT.map_of_exact colim).hasProjectiveDimensionLT_X₃ (n + 1) h₁
        (hasProjectiveDimensionLT_of_ge (colimit T.X₂) 1 _ (by lia))
    exact hasProjectiveDimensionLT_of_iso (colimit.isoColimitCocone ⟨c, hc⟩) _

/-- When coproducts indexed by `ι` are exact, a coproduct of objects of projective dimension
`< n` has projective dimension `< n`. -/
instance (X : ι → C) (n : ℕ) [∀ i, HasProjectiveDimensionLT (X i) n] :
    HasProjectiveDimensionLT (∐ X) n :=
  hasProjectiveDimensionLT_of_isColimit_cofan (coproductIsCoproduct X) n inferInstance

end Coproducts

end CategoryTheory
