/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.Depth.Basic
import TauCeti.Algebra.Homology.Ext.LeftDerived
import TauCeti.RingTheory.Depth.Basic

/-!
# Local cohomology vanishes below the depth

Let `R` be a Noetherian ring, `I` an ideal of `R` and `M` a finite `R`-module. The local cohomology
module `H^i_I(M) = (localCohomology I i).obj M` vanishes for every `i` smaller than the depth
`I.depth M` of `M` with respect to `I` (Stacks, Lemma 47.11.1 (0AVZ), first part). For instance,
over a Noetherian local ring `(A, 𝔪)` of depth at least `3`, the modules `H¹_𝔪(A)` and `H²_𝔪(A)`
vanish; this is the hypothesis through which depth enters the full faithfulness of restricting
finite étale covers of a punctured spectrum to a hypersurface section (Stacks, Lemmas 58.19.6
(0BM6) and 58.19.7 (0BLJ)).

Mathlib defines `H^i_I(M)` as the colimit of the groups `Extⁱ(R ⧸ Iⁿ, M)`, computed by the left
derived functor `Ext R (ModuleCat R) i`, while `I.depth M` is defined by the vanishing of the
derived-category groups `Ext (R ⧸ I) M i`. The two constructions of `Ext` vanish together
(`CategoryTheory.Abelian.Ext.subsingleton_iff_isZero_Ext`), so it suffices to show that each
`Ext (R ⧸ Iⁿ) M i` vanishes for `i < I.depth M`. This follows from the Rees theorem
`ModuleCat.exists_isRegular_tfae`: below the `I`-depth of `M`, `Ext N M i` vanishes for every finite
module `N` supported in `V(I)`. Equivalently, `I.depth M ≤ N.depth M` for such `N`
(`ModuleCat.depth_le_depth_of_support_subset` in `TauCeti.RingTheory.Depth.Basic`), which also
holds when `I M = M`, as then `N` and `M` have comaximal annihilators.

The zero module has depth `⊤`, and its local cohomology vanishes in every degree over any
commutative ring, Noetherian or not: every `Extⁱ(R ⧸ Iⁿ, 0)` is computed by a complex of zero
modules.

## Main results

* `localCohomology.isZero_obj_of_lt_depth`: `H^i_I(M) = 0` for `i < I.depth M`.
* `localCohomology.isZero_obj_of_subsingleton`: `H^i_I(0) = 0` for every `i`.

## References

* [Stacks Project, Lemma 47.11.1](https://stacks.math.columbia.edu/tag/0AVZ)
* H. Matsumura, *Commutative Algebra*, Theorem 28 (the Rees theorem, Mathlib's
  `ModuleCat.exists_isRegular_tfae`).
-/

public section

universe v u

open CategoryTheory Limits Abelian

namespace localCohomology

variable {R : Type u} [CommRing R]

/-- `H^i_I(M)` vanishes as soon as every `Extⁱ(R ⧸ Iⁿ, M)` does: by definition it is the colimit
over `n` of these groups. -/
private theorem isZero_obj_of_forall_isZero_ext (I : Ideal R) (M : ModuleCat.{u} R) {i : ℕ}
    (hExt : ∀ n : ℕ,
      IsZero (((Ext R (ModuleCat.{u} R) i).obj (Opposite.op (.of R (R ⧸ I ^ n)))).obj M)) :
    IsZero ((localCohomology I i).obj M) := by
  -- The `n`-th term of the diagram is `hExt n` by definition of `localCohomology`.
  refine IsZero.of_iso ?_ (colimitObjIsoColimitCompEvaluation _ M)
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun n ↦ (hExt n.unop.unop).eq_of_src _ _

/-- **Local cohomology vanishes below the depth.** For a finite module `M` over a Noetherian ring
and an ideal `I`, the local cohomology module `H^i_I(M)` vanishes for every `i < I.depth M`. -/
@[stacks 0AVZ "The vanishing part. Stacks states it for `I M ≠ M`; when `I M = M` the depth is
`⊤` and every local cohomology module vanishes."]
theorem isZero_obj_of_lt_depth [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] {i : ℕ} (hi : (i : ℕ∞) < I.depth M) :
    IsZero ((localCohomology I i).obj M) := by
  have hExt (n : ℕ) :
      IsZero (((Ext R (ModuleCat.{u} R) i).obj (Opposite.op (.of R (R ⧸ I ^ n)))).obj M) := by
    refine (Abelian.Ext.subsingleton_iff_isZero_Ext R _ M i).1
      (ModuleCat.subsingleton_ext_of_lt_depth ?_)
    refine hi.trans_le (ModuleCat.depth_le_depth_of_support_subset I _ M fun p hp ↦ ?_)
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient] at hp
    exact Ideal.IsPrime.le_of_pow_le hp
  exact isZero_obj_of_forall_isZero_ext I M hExt

/-- **Local cohomology of the zero module vanishes.** For any commutative ring `R`, ideal `I` and
degree `i`, the local cohomology module `H^i_I(M)` of a zero module `M` is zero. -/
theorem isZero_obj_of_subsingleton (I : Ideal R) (i : ℕ) (M : ModuleCat.{u} R) [Subsingleton M] :
    IsZero ((localCohomology I i).obj M) := by
  have hM : IsZero M := ModuleCat.isZero_iff_subsingleton.2 ‹_›
  refine isZero_obj_of_forall_isZero_ext I M fun n ↦ ?_
  -- Compute `Extⁱ(R ⧸ Iⁿ, M)` by a projective resolution `P`: the `i`-th term of the complex
  -- `Hom(P, M)` is a module of morphisms into the zero module, hence zero.
  rw [(projectiveResolution _).isZero_Ext_iff_exactAt R, HomologicalComplex.exactAt_iff]
  refine ShortComplex.exact_of_isZero_X₂ _ (ModuleCat.isZero_iff_subsingleton.2 ?_)
  exact ⟨fun f g ↦ hM.eq_of_tgt f g⟩

end localCohomology
