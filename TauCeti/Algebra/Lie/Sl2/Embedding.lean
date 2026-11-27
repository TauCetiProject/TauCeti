/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.JacobsonMorozov
public import TauCeti.Algebra.Lie.Sl2.TripleOrZero.Basic

/-!
# The Lie embedding of `sl₂` attached to an `sl₂` triple

An `sl₂` triple `t : IsSl2Triple h e f` in a Lie algebra `L` over `K` is the same thing as a Lie
algebra homomorphism `sl (Fin 2) K →ₗ⁅K⁆ L` that does not kill the Cartan element: such a
homomorphism carries the standard triple

`E = E₀₁`, `F = E₁₀`, `H = E₀₀ - E₁₁`

to a triple, and conversely `t.isSl2TripleOrZero.toLieHom K` (see
`TauCeti.IsSl2TripleOrZero.toLieHom`) sends `E`, `F`, `H` to `e`, `f`, `h`. Over a
domain of characteristic zero, with `L` torsion-free, this homomorphism is injective, being the
identification of `sl (Fin 2) K` with the Lie subalgebra `t.toLieSubalgebra K` spanned by the
triple. This is the form in which statements about triples become statements about embeddings
`sl₂ ↪ 𝔤`, and it is the map along which a representation of `L` restricts to `sl₂`.

Read through this dictionary, the Jacobson–Morozov theorem says that in a finite-dimensional Lie
algebra with nondegenerate Killing form over a field of characteristic zero, the images of `E`
under the embeddings `sl₂ ↪ 𝔤` are exactly the nonzero `ad`-nilpotent elements, and Kostant's
conjugacy theorem says that two embeddings with the same value at `E` differ by an automorphism in
`TauCeti.expAdSubgroup`.

## Main definitions

* `IsSl2Triple.toLieSubalgebraEquiv`: over a domain of characteristic zero, with `L`
  torsion-free, the Lie algebra isomorphism of `sl (Fin 2) K` with the subalgebra
  `t.toLieSubalgebra K` spanned by the triple.

## Main results

* `IsSl2Triple.range_toLieHom`: the range of `t.isSl2TripleOrZero.toLieHom K` is
  `t.toLieSubalgebra K`.
* `IsSl2Triple.toLieHom_injective` and `LieHom.injective_iff_map_singleSubSingle_ne_zero`: over a
  domain of characteristic zero, into a torsion-free Lie algebra, a homomorphism out of
  `sl (Fin 2) K` is injective if and only if it does not kill `H`; by
  `LieHom.map_singleSubSingle_ne_zero_of_map_single_ne_zero`, it suffices that it does not kill `E`.
* `TauCeti.exists_injective_lieHom_slFinTwo_iff`: **Jacobson–Morozov for embeddings.** An element
  `e` is the image of `E` under an embedding `sl₂ ↪ L` if and only if `e ≠ 0` and `ad e` is
  nilpotent.
* `TauCeti.exists_lieEquiv_comp_eq_of_apply_eq`: **Kostant's conjugacy for embeddings.** An
  embedding `sl₂ ↪ L` and a homomorphism agreeing with it at `E` are conjugate by an automorphism in
  `TauCeti.expAdSubgroup`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapters 7–9, Chapter VIII, §11.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*, Van
  Nostrand Reinhold, 1993, §3.3.
-/

public section

open LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

namespace IsSl2Triple

open TauCeti

section CommRing

variable (K : Type*) {L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L] {h e f : L}
  (t : IsSl2Triple h e f)

/-- The range of the homomorphism of a triple is the Lie subalgebra spanned by the triple. -/
theorem range_toLieHom : (t.isSl2TripleOrZero.toLieHom K).range = t.toLieSubalgebra K := by
  ext x
  rw [LieHom.mem_range, mem_toLieSubalgebra_iff, t.lie_e_f]
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.val 0 1, A.val 1 0, A.val 0 0, t.isSl2TripleOrZero.toLieHom_apply K A⟩
  · rintro ⟨c₁, c₂, c₃, rfl⟩
    exact ⟨c₁ • SpecialLinear.single 0 1 zero_ne_one 1 + c₂ • SpecialLinear.single 1 0 one_ne_zero 1
      + c₃ • SpecialLinear.singleSubSingle 0 1 1, by simp⟩

end CommRing

section Domain

variable (K : Type*) {L : Type*} [CommRing K] [IsDomain K] [CharZero K] [LieRing L]
  [LieAlgebra K L] [Module.IsTorsionFree K L] {h e f : L} (t : IsSl2Triple h e f)

/-- **The homomorphism of a triple is an embedding.** Over a domain of characteristic zero, with
`L` torsion-free, it sends the standard basis of `sl (Fin 2) K` to the linearly independent
family `e`, `f`, `h` (`TauCeti.linearIndependent_isSl2Triple`). -/
theorem toLieHom_injective : Function.Injective (t.isSl2TripleOrZero.toLieHom K) := by
  have hc : (t.isSl2TripleOrZero.toLieHom K : SpecialLinear.sl (Fin 2) K →ₗ[K] L) =
      (slFinTwoBasis K).constr K ![e, f, h] :=
    (slFinTwoBasis K).ext fun i ↦ by simpa using t.isSl2TripleOrZero.toLieHom_slFinTwoBasis K i
  rw [← LieHom.coe_toLinearMap, hc]
  exact (slFinTwoBasis K).injective_constr_of_linearIndependent (linearIndependent_isSl2Triple t)

/-- **`sl₂` is isomorphic to the subalgebra spanned by a triple.** Over a domain of characteristic
zero, with `L` torsion-free, the homomorphism of a triple is a Lie algebra isomorphism of
`sl (Fin 2) K` onto `t.toLieSubalgebra K`. -/
noncomputable def toLieSubalgebraEquiv : SpecialLinear.sl (Fin 2) K ≃ₗ⁅K⁆ t.toLieSubalgebra K :=
  (LieEquiv.ofInjective _ (t.toLieHom_injective K)).trans
    (LieEquiv.ofEq _ _ (by rw [t.range_toLieHom K]))

/-- The isomorphism of `sl (Fin 2) K` with the subalgebra spanned by a triple is the homomorphism
of the triple. -/
@[simp]
theorem coe_toLieSubalgebraEquiv_apply (A : SpecialLinear.sl (Fin 2) K) :
    (t.toLieSubalgebraEquiv K A : L) = t.isSl2TripleOrZero.toLieHom K A :=
  (rfl)

end Domain

end IsSl2Triple

namespace LieHom

open TauCeti

section Injective

variable {K L : Type*} [CommRing K] [IsDomain K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [Module.IsTorsionFree K L]

/-- Over a domain of characteristic zero, a Lie algebra homomorphism out of `sl (Fin 2) K` into a
torsion-free Lie algebra is injective if and only if it does not kill the Cartan element
`H = E₀₀ - E₁₁`. -/
theorem injective_iff_map_singleSubSingle_ne_zero (φ : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L) :
    Function.Injective φ ↔ φ (SpecialLinear.singleSubSingle 0 1 1) ≠ 0 := by
  refine ⟨fun hφ ↦ ?_, fun hφ ↦ ?_⟩
  · rw [Ne, ← map_zero φ, hφ.eq_iff]
    exact singleSubSingle_ne_zero zero_ne_one one_ne_zero
  · rw [φ.eq_toLieHom_map]
    exact IsSl2Triple.toLieHom_injective K
      ((isSl2Triple_single (R := K) zero_ne_one).map φ hφ)

/-- Over a domain of characteristic zero, a Lie algebra homomorphism out of `sl (Fin 2) K` into a
torsion-free Lie algebra that does not kill the raising element `E = E₀₁` does not kill the Cartan
element `H = E₀₀ - E₁₁` either, since `⁅H, E⁆ = 2 • E`. -/
theorem map_singleSubSingle_ne_zero_of_map_single_ne_zero
    (φ : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L)
    (hφ : φ (SpecialLinear.single 0 1 zero_ne_one 1) ≠ 0) :
    φ (SpecialLinear.singleSubSingle 0 1 1) ≠ 0 := fun h0 ↦ by
  have h2 : (2 : K) • φ (SpecialLinear.single 0 1 zero_ne_one 1) = 0 := by
    rw [← map_smul, ← lie_singleSubSingle_single, LieHom.map_lie, h0, zero_lie]
  exact hφ ((smul_eq_zero.1 h2).resolve_left two_ne_zero)

end Injective

end LieHom

namespace TauCeti

section JacobsonMorozov

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

omit [FiniteDimensional K L] in
/-- **The Jacobson–Morozov theorem for embeddings.** In a Lie algebra with nondegenerate Killing
form over a field of characteristic zero, `e` is the image of the raising element `E₀₁` under an
injective Lie algebra homomorphism `sl (Fin 2) K →ₗ⁅K⁆ L` if and only if `e ≠ 0` and `ad e` is
nilpotent. -/
theorem exists_injective_lieHom_slFinTwo_iff [IsKilling K L] {e : L} :
    (∃ φ : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L,
      Function.Injective φ ∧ φ (SpecialLinear.single 0 1 zero_ne_one 1) = e) ↔
      IsNilpotent (ad K L e) ∧ e ≠ 0 := by
  rw [← exists_isSl2Triple_iff]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨_, _, (isSl2Triple_single (R := K) zero_ne_one).map φ
      (φ.injective_iff_map_singleSubSingle_ne_zero.1 hφ)⟩
  · rintro ⟨h, f, t⟩
    exact ⟨t.isSl2TripleOrZero.toLieHom K, t.toLieHom_injective K,
      t.isSl2TripleOrZero.toLieHom_single_zero_one K⟩

variable [LieAlgebra ℚ L]

/-- **Kostant's conjugacy theorem for embeddings.** Let `φ` be an injective Lie algebra
homomorphism `sl (Fin 2) K →ₗ⁅K⁆ L` into a finite-dimensional Lie algebra over a field of
characteristic zero, and `φ'` any Lie algebra homomorphism agreeing with `φ` at the raising element
`E₀₁` (it is then injective too). Some automorphism `ψ` of `L` in the subgroup
`TauCeti.expAdSubgroup K e` attached to their common value `e` satisfies `ψ ∘ φ = φ'`. -/
theorem exists_lieEquiv_comp_eq_of_apply_eq {φ φ' : SpecialLinear.sl (Fin 2) K →ₗ⁅K⁆ L}
    (hφ : Function.Injective φ)
    (he : φ (SpecialLinear.single 0 1 zero_ne_one 1) =
      φ' (SpecialLinear.single 0 1 zero_ne_one 1)) :
    ∃ ψ : L ≃ₗ⁅K⁆ L, ψ.toLinearEquiv ∈ expAdSubgroup K (φ (SpecialLinear.single 0 1 zero_ne_one 1))
      ∧ (ψ : L →ₗ⁅K⁆ L).comp φ = φ' := by
  have t := (isSl2Triple_single (R := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).map φ
    (φ.injective_iff_map_singleSubSingle_ne_zero.1 hφ)
  have t' := (isSl2Triple_single (R := K) (zero_ne_one : (0 : Fin 2) ≠ 1)).map φ'
    (φ'.map_singleSubSingle_ne_zero_of_map_single_ne_zero (he ▸ t.e_ne_zero))
  rw [← he] at t'
  obtain ⟨ψ, hψ, -, -, hψf⟩ := t.exists_lieEquiv_apply_eq (K := K) t'
  refine ⟨ψ, hψ, ?_⟩
  ext
  · simpa [he] using apply_eq_self_of_mem_expAdSubgroup hψ
  · simpa using hψf

end JacobsonMorozov

end TauCeti
