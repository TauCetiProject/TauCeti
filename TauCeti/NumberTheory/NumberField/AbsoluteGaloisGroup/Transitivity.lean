/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Profinite
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Decomposition

/-!
# Transitivity of the absolute Galois group on primes above a prime

Let `F` be a perfect field (for instance a number field), `G_F = Field.absoluteGaloisGroup F` and
`O` the integral closure of `𝓞 F` in `F^alg = AlgebraicClosure F`. The elements of `O` fixed by
all of `G_F` are exactly those of `𝓞 F` (`TauCeti.GaloisRep.isInvariant_integralClosure`), and
`O` with the discrete topology is a continuous `G_F`-module, since the stabilizer of an algebraic
element is open in the Krull topology. Mathlib's transitivity theorem for profinite groups,
`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`, then says that `G_F` acts transitively
on the prime ideals of `O` lying over a given prime of `𝓞 F`
(`TauCeti.GaloisRep.exists_smul_eq_of_under_eq`).

Combined with `I_{σQ} = σ I_Q σ⁻¹` (Mathlib's `Ideal.inertia_smul`), the inertia groups at the
primes of `O` above a prime of `𝓞 F` form a single conjugacy class of subgroups of `G_F`
(`TauCeti.GaloisRep.exists_inertiaGroup_eq_map_conj`).

## Main results

* `TauCeti.GaloisRep.isInvariant_integralClosure`: `O^{G_F} = 𝓞 F`.
* `TauCeti.GaloisRep.exists_smul_eq_of_under_eq`: two primes of `O` over the same prime of `𝓞 F`
  are `G_F`-conjugate.
* `TauCeti.GaloisRep.exists_inertiaGroup_eq_map_conj`: their inertia groups are conjugate.
-/

public section

noncomputable section

open NumberField Pointwise

namespace TauCeti.GaloisRep

variable {F : Type*} [Field F]

/-- An element of `O` is fixed by `σ ∈ G_F` exactly when its image in `F^alg` is. -/
theorem smul_integralClosure_eq_iff (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    σ • x = x ↔ DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ
      (x : AlgebraicClosure F) = x := by
  rw [← coe_smul_integralClosure, Subtype.ext_iff]

variable (F) in
/-- For a perfect field `F`, the elements of the integral closure `O` of `𝓞 F` in `F^alg` fixed by
`G_F` are those of `𝓞 F`: a fixed element lies in `F` because `F^alg / F` is Galois, and it is
integral over `𝓞 F`, hence over `ℤ`. -/
theorem isInvariant_integralClosure [PerfectField F] :
    Algebra.IsInvariant (𝓞 F) (integralClosure (𝓞 F) (AlgebraicClosure F))
      (Field.absoluteGaloisGroup F) where
  isInvariant x hx := by
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed
      (k := F) (x : AlgebraicClosure F)).2 fun σ ↦ (smul_integralClosure_eq_iff σ x).1 (hx σ)
    have hyO : IsIntegral (𝓞 F) y := by
      rw [← isIntegral_algebraMap_iff (B := AlgebraicClosure F), hy]
      exact x.property
    refine ⟨⟨y, isIntegral_trans (R := ℤ) y hyO⟩, Subtype.ext ?_⟩
    rw [← hy]
    rfl

variable (F) in
/-- The action of `G_F` on `O` is continuous for the discrete topology on `O`: the stabilizer of an
element is the stabilizer of an algebraic element of `F^alg`, which is open in the Krull
topology. -/
theorem continuousSMul_integralClosure :
    letI : TopologicalSpace (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⊥
    ContinuousSMul (Field.absoluteGaloisGroup F) (integralClosure (𝓞 F) (AlgebraicClosure F)) := by
  let _ : TopologicalSpace (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⊥
  have : DiscreteTopology (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⟨rfl⟩
  refine continuousSMul_iff_stabilizer_isOpen.2 fun x ↦ ?_
  have h : (MulAction.stabilizer (Field.absoluteGaloisGroup F) x :
      Set (Field.absoluteGaloisGroup F)) =
      {σ | DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ
        (x : AlgebraicClosure F) = x} :=
    Set.ext fun σ ↦ MulAction.mem_stabilizer_iff.trans (smul_integralClosure_eq_iff σ x)
  rw [h]
  exact stabilizer_isOpen_of_isIntegral (K := F) (x : AlgebraicClosure F)

/-- For a perfect field `F`, `G_F` acts transitively on the prime ideals of the integral closure
`O` of `𝓞 F` in `F^alg` lying over a given prime of `𝓞 F`. -/
theorem exists_smul_eq_of_under_eq [PerfectField F]
    (P Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (𝓞 F) = Q.under (𝓞 F)) :
    ∃ σ : Field.absoluteGaloisGroup F, Q = σ • P := by
  let _ : TopologicalSpace (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⊥
  have : DiscreteTopology (integralClosure (𝓞 F) (AlgebraicClosure F)) := ⟨rfl⟩
  have := continuousSMul_integralClosure F
  have := isInvariant_integralClosure F
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite P Q hPQ

/-- For a perfect field `F`, the inertia groups at two primes of `O` over the same prime of `𝓞 F`
are conjugate in `G_F`. -/
theorem exists_inertiaGroup_eq_map_conj [PerfectField F]
    (P Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.under (𝓞 F) = Q.under (𝓞 F)) :
    ∃ σ : Field.absoluteGaloisGroup F,
      inertiaGroup F Q = (inertiaGroup F P).map (MulAut.conj σ).toMonoidHom := by
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_under_eq P Q hPQ
  exact ⟨σ, Ideal.inertia_smul σ P⟩

end TauCeti.GaloisRep
