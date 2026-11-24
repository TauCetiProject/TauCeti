/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Localization.Module
import TauCeti.Algebra.Module.Torsion.Finite

/-!
# Torsion-free modules of generic rank one

Let `R` be a domain with fraction field `F`, and `M` a torsion-free `R`-module whose generic fibre
`F ⊗[R] M` is a line. Then `M` embeds in that line, so any two elements of `M` are commensurable:
for `s ≠ 0`, every `t` satisfies `a • t = b • s` with `a ≠ 0`. Hence `M ⧸ R • s` is a torsion
module, and when `M` is finitely generated and `R` has finite quotients by nonzero ideals, such as
the ring of integers of a number field, the multiples of `s` have finite index in `M`. This is the
finiteness of the index `#(L / 𝓞 K • s)` of a section `s` of a line bundle `L` over `Spec 𝓞 K`.

## Main results

* `Module.exists_smul_eq_smul_of_finrank_eq_one`: elements of a torsion-free module of generic
  rank one are commensurable.
* `Module.finite_quotient_span_singleton_of_finrank_eq_one`: a nonzero element of a finitely
  generated torsion-free module of generic rank one over a ring with finite quotients has
  multiples of finite index.
-/

public section

open TensorProduct

namespace Module

variable {R F M : Type*} [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]

/-- **Elements of a module of generic rank one are commensurable.** If `M` is a torsion-free
module over a domain `R` with fraction field `F` and `F ⊗[R] M` is a line, then for `s ≠ 0` every
`t : M` satisfies `a • t = b • s` for some `a ≠ 0` and `b` in `R`. -/
theorem exists_smul_eq_smul_of_finrank_eq_one (h : finrank F (F ⊗[R] M) = 1) {s : M}
    (hs : s ≠ 0) (t : M) : ∃ a b : R, a ≠ 0 ∧ a • t = b • s := by
  -- `R` is a domain, since its fraction ring `F` is a field.
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (R := R) (K := F)).2 (Field.toIsField F)
  -- `M` is torsion-free, so it embeds in its localization `F ⊗[R] M`, a line spanned by `1 ⊗ s`.
  have := IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors R) F (M := M)
  have hinj : Function.Injective (TensorProduct.mk R F M 1) :=
    (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R) _).2 fun c =>
      IsSMulRegular.of_ne_zero (nonZeroDivisors.ne_zero c.property)
  have hs' : (1 : F) ⊗ₜ[R] s ≠ 0 := fun h0 => hs (hinj (by simpa using h0))
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' _ hs').1 h ((1 : F) ⊗ₜ t)
  -- Write the coordinate `c` of `1 ⊗ t` as a quotient `b / a` of elements of `R`.
  obtain ⟨b, a, ha, rfl⟩ := IsFractionRing.div_surjective R c
  have ha' : algebraMap R F a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  refine ⟨a, b, nonZeroDivisors.ne_zero ha, hinj ?_⟩
  simp [← hc, ← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ ha']

/-- **Multiples of an element of a module of generic rank one have finite index.** If `M` is a
finitely generated torsion-free module over a domain `R` with finite quotients and fraction field
`F`, and `F ⊗[R] M` is a line, then `M ⧸ R • s` is finite for every `s ≠ 0`. -/
theorem finite_quotient_span_singleton_of_finrank_eq_one [Ring.HasFiniteQuotients R]
    [Module.Finite R M] (h : finrank F (F ⊗[R] M) = 1) {s : M} (hs : s ≠ 0) :
    Finite (M ⧸ Submodule.span R {s}) := by
  have : IsDomain R := (IsFractionRing.isDomain_iff_isField (R := R) (K := F)).2 (Field.toIsField F)
  refine Module.IsTorsion.finite (R := R) fun {x} => ?_
  induction x using Submodule.Quotient.induction_on with | _ t => ?_
  obtain ⟨a, b, ha, hab⟩ := exists_smul_eq_smul_of_finrank_eq_one h hs t
  refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
  rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hab]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s)

end Module
