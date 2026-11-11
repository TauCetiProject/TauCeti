/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
public import Mathlib.Data.Nat.Factorial.NatCast
import TauCeti.LinearAlgebra.Multilinear.Polarization

/-!
# Pure powers span the symmetric algebra

When `n!` is invertible, the degree-`n` homogeneous submodule of a symmetric
algebra is spanned by powers `ι(x)^n`. Over a commutative rational algebra,
pure powers in all degrees therefore span the whole symmetric algebra, without
freeness or finite generation assumptions on the module.
`linearMap_ext_ι_pow` compares linear maps on these spanning powers. This permits checking
linear identities, such as compatibility with a coproduct, on pure powers.

Polarization expresses symmetric monomials as linear combinations of pure powers,
using `MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl`.
For the classical polarization identity, see
Fulton and Harris, *Representation Theory: A First Course*, Appendix B.1.

Adapted from [yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0).
Modified for the Tau Ceti API.
-/

public section

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra

open scoped BigOperators

variable (R M : Type*) [CommRing R] [AddCommMonoid M] [Module R M]

/-- If `n!` is invertible, pure `n`th powers of generators span the entire
degree-`n` homogeneous submodule, even for modules without a basis. -/
theorem span_range_ι_pow (n : ℕ) (hn : IsUnit (n.factorial : R)) :
    Submodule.span R (Set.range fun x : M => ι R M x ^ n) =
      TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    simpa using TauCeti.SymmetricAlgebra.prod_map_ι_mem_homogeneousSubmodule
      R M (List.replicate n x)
  · rw [TauCeti.SymmetricAlgebra.homogeneousSubmodule_eq_span]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    let f := (MultilinearMap.mkPiAlgebra R (Fin n) (SymmetricAlgebra R M)).compLinearMap
      (fun _ => ι R M)
    let m : Fin n → M := fun i => l.get (i.cast hl.symm)
    have hm : List.ofFn m = l := by
      subst n
      exact List.ofFn_get l
    have hprod : (∏ i, ι R M (m i)) = (l.map (ι R M)).prod := by
      simpa only [List.map_ofFn, Function.comp_def, List.prod_ofFn] using
        congrArg (fun l => (l.map (ι R M)).prod) hm
    have hperm (σ : Equiv.Perm (Fin n)) :
        f (fun i => m (σ i)) = (l.map (ι R M)).prod := by
      simpa only [f, MultilinearMap.compLinearMap_apply,
        MultilinearMap.mkPiAlgebra_apply, hprod] using
        Equiv.prod_comp σ (fun i => ι R M (m i))
    have hpol := f.sum_neg_one_pow_card_smul_apply_sum_compl m
    have hmem : (n.factorial : R) • (l.map (ι R M)).prod ∈
        Submodule.span R (Set.range fun x : M => ι R M x ^ n) := by
      have hsum : (∑ S : Finset (Fin n), (-1 : R) ^ S.card •
          f (fun _ => ∑ i ∈ Sᶜ, m i)) ∈
          Submodule.span R (Set.range fun x : M => ι R M x ^ n) := by
        apply Submodule.sum_mem
        intro S _
        apply Submodule.smul_mem
        simp only [f, MultilinearMap.compLinearMap_apply,
          MultilinearMap.mkPiAlgebra_apply, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
        exact Submodule.subset_span ⟨_, rfl⟩
      rw [hpol] at hsum
      simpa only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, Nat.cast_smul_eq_nsmul] using hsum
    exact (Submodule.smul_mem_iff_of_isUnit _ hn).mp hmem

/-- Over a commutative rational algebra, powers of generators in all degrees
span the symmetric algebra. -/
@[simp]
theorem span_range_ι_pow_eq_top [Algebra ℚ R] :
    Submodule.span R (Set.range fun p : M × ℕ => ι R M p.1 ^ p.2) = ⊤ := by
  apply top_unique
  rw [← TauCeti.SymmetricAlgebra.iSup_homogeneousSubmodule_eq_top R M]
  refine iSup_le fun n => ?_
  rw [← span_range_ι_pow R M n (IsUnit.natCast_factorial_of_algebra ℚ n)]
  apply Submodule.span_mono
  rintro _ ⟨x, rfl⟩
  exact ⟨(x, n), rfl⟩

/-- Two linear maps from a symmetric algebra over a rational algebra agree
if they agree on every pure power of every generator. -/
theorem linearMap_ext_ι_pow [Algebra ℚ R] {N : Type*} [AddCommMonoid N] [Module R N]
    {f g : SymmetricAlgebra R M →ₗ[R] N}
    (h : ∀ x : M, ∀ n : ℕ, f (ι R M x ^ n) = g (ι R M x ^ n)) : f = g := by
  apply LinearMap.ext_on_range (span_range_ι_pow_eq_top R M)
  rintro ⟨x, n⟩
  exact h x n

end TauCeti.SymmetricAlgebra
