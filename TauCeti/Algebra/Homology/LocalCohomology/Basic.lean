/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.LocalCohomology
import TauCeti.Algebra.Homology.Ext.LeftDerived

/-!
# Vanishing of local cohomology

Mathlib defines the local cohomology module `H^i_I(M) = (localCohomology I i).obj M` of a module
`M` over a commutative ring `R` as the colimit over `n` of the groups `Extⁱ(R ⧸ Iⁿ, M)`, computed
by the left derived functor `Ext R (ModuleCat R) i`. So `H^i_I(M)` vanishes as soon as each of
these groups does. In particular the local cohomology of the zero module vanishes in every degree
over any commutative ring, Noetherian or not: every `Extⁱ(R ⧸ Iⁿ, 0)` is computed by a complex of
zero modules.

## Main results

* `localCohomology.isZero_obj_of_forall_isZero_ext`: `H^i_I(M) = 0` if every `Extⁱ(R ⧸ Iⁿ, M)`
  vanishes.
* `localCohomology.isZero_obj_of_subsingleton`: `H^i_I(0) = 0` for every `i`.
-/

public section

universe u

open CategoryTheory Limits Abelian

namespace localCohomology

variable {R : Type u} [CommRing R]

/-- `H^i_I(M)` vanishes as soon as every `Extⁱ(R ⧸ Iⁿ, M)` does: by definition it is the colimit
over `n` of these groups. -/
theorem isZero_obj_of_forall_isZero_ext (I : Ideal R) (M : ModuleCat.{u} R) {i : ℕ}
    (hExt : ∀ n : ℕ,
      IsZero (((Ext R (ModuleCat.{u} R) i).obj (Opposite.op (.of R (R ⧸ I ^ n)))).obj M)) :
    IsZero ((localCohomology I i).obj M) := by
  -- The `n`-th term of the diagram is `hExt n` by definition of `localCohomology`.
  refine IsZero.of_iso ?_ (colimitObjIsoColimitCompEvaluation _ M)
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun n ↦ (hExt n.unop.unop).eq_of_src _ _

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
