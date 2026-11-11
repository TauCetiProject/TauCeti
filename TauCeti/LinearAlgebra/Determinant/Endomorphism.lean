/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Defs
public import TauCeti.LinearAlgebra.Determinant.Exact
import TauCeti.Data.SignType.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The determinant line of an endomorphism

Let `T : V → V` be an endomorphism of a finite-dimensional vector space. Its kernel and cokernel
sit in the exact sequence

`0 → ker T → V → V → coker T → 0`,

so the four-term identity of determinant lines (`TauCeti.detLineFourTermEquiv`) identifies
`det V ⊗ (det V)^*` with the determinant line `det T = det (ker T) ⊗ (det (coker T))^*`. The first
of these is canonically the scalars, by the contraction `β ⊗ φ ↦ φ β`. This gives a trivialization
`det T ≃ K` (`LinearMap.detLineEndEquiv`) for every endomorphism, with no choice of bases, also
when `T` is not invertible. In that case it retains the whole determinant line of the kernel and
cokernel, where the determinant of `T` itself is `0`.

When `T` is bijective its determinant line is also trivialized by
`LinearMap.detLineEquivOfBijective`, which sends the product of the empty exterior products of
kernel and cokernel to `1`. The two trivializations differ by the determinant
(`LinearMap.detLineEndEquiv_eq_inv_det_mul`):

`detLineEndEquiv T x = (det T)⁻¹ * detLineEquivOfBijective T x`.

The inverse is the convention in which the two-term complex `T : V → V`, from degree `1` to
degree `0`, has torsion `(det T)⁻¹` (`HomologicalComplex.reidemeisterTorsion_eq_det_zpow`).
Consequently, when an operator `L` has kernel and cokernel identified with those of a finite
endomorphism `T`, the orientation that `det T`'s canonical trivialization induces on `det L`
differs from the one given by invertibility of `L` by the sign of `det T`. This is how the sign of
`det (1 - P)` for a linearized return map `P` enters the orientation of periodic orbits.

## Main declarations

* `LinearMap.detLineEndEquiv`: the canonical trivialization `det T ≃ K` of the determinant line of
  an endomorphism.
* `LinearMap.detLineEndEquiv_detLineFourTermEquiv`: its defining value `φ β` on the image of
  `β ⊗ φ` under the four-term isomorphism.
* `LinearMap.detLineEndEquiv_tmul`: its value on exterior products.
* `LinearMap.detLineEndEquiv_eq_inv_det_mul`: for bijective `T`, comparison with
  `LinearMap.detLineEquivOfBijective` through the factor `(det T)⁻¹`.
* `LinearMap.sign_detLineEndEquiv`: over an ordered field, the two trivializations of a bijective
  `T` induce orientations that differ by the sign of `det T`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. **14** (2002),
  209–244, Appendix A, for the torsion convention.
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (T : V →ₗ[K] V)

/-- **The canonical trivialization of the determinant line of an endomorphism.** For an
endomorphism `T` of a finite-dimensional vector space `V`, the exact sequence
`0 → ker T → V → V → coker T → 0` identifies `det V ⊗ (det V)^*` with the determinant line of `T`
(`TauCeti.detLineFourTermEquiv`), and `det V ⊗ (det V)^*` is identified with `K` by the
contraction `β ⊗ φ ↦ φ β` (`LinearMap.detLineEndEquiv_detLineFourTermEquiv`). For bijective `T`
this is `(det T)⁻¹` times `LinearMap.detLineEquivOfBijective`
(`LinearMap.detLineEndEquiv_eq_inv_det_mul`). -/
def detLineEndEquiv : T.detLine ≃ₗ[K] K :=
  (TauCeti.detLineFourTermEquiv (ker T).injective_subtype T.exact_subtype_ker_map
      T.exact_map_mkQ_range (range T).mkQ_surjective).symm ≪≫ₗ
    TensorProduct.comm K _ _ ≪≫ₗ Module.Invertible.linearEquiv K _

/-- The defining value of `LinearMap.detLineEndEquiv`: the image of `β ⊗ φ` under the four-term
isomorphism of `0 → ker T → V → V → coker T → 0` goes to `φ β`. -/
@[simp]
theorem detLineEndEquiv_detLineFourTermEquiv (β : TauCeti.detLine K V)
    (φ : Dual K (TauCeti.detLine K V)) :
    T.detLineEndEquiv (TauCeti.detLineFourTermEquiv (ker T).injective_subtype
      T.exact_subtype_ker_map T.exact_map_mkQ_range (range T).mkQ_surjective (β ⊗ₜ φ)) = φ β := by
  simp [detLineEndEquiv]

/-- **The value of `LinearMap.detLineEndEquiv` on exterior products.** Let `u` be a family of
`dim (ker T)` vectors of the kernel, `v` a family of `dim (range T)` vectors of `V`, and `z` a
family of `dim (coker T)` vectors of `V`. Let `β ∈ det V` be the exterior product of `u` followed
by `v`, and `γ ∈ det V` that of `T ∘ v` followed by `z`. If `ξ` takes the value `1` at the
exterior product of the classes of `z` in the cokernel, then `φ γ * detLineEndEquiv T (α ⊗ ξ) = φ β`
for every functional `φ` on `det V`, where `α` is the exterior product of `u`. When `u` is a basis
of the kernel, `T ∘ v` a basis of the range and the classes of `z` a basis of the cokernel, so that
`β` and `γ` are nonzero, this says that `detLineEndEquiv T (α ⊗ ξ)` is the ratio of `β` to `γ`. -/
theorem detLineEndEquiv_tmul (u : Fin (finrank K (ker T)) → ker T)
    (v : Fin (finrank K (range T)) → V) (z : Fin (finrank K (V ⧸ range T)) → V)
    {β : TauCeti.detLine K V} (hβ : (β : ExteriorAlgebra K V) =
      ExteriorAlgebra.ιMulti K _ (Fin.append ((ker T).subtype ∘ u) v))
    {γ : TauCeti.detLine K V} (hγ : (γ : ExteriorAlgebra K V) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (T ∘ v) z))
    (φ : Dual K (TauCeti.detLine K V)) {ξ : Dual K (TauCeti.detLine K (V ⧸ range T))}
    (hξ : ξ (exteriorPower.ιMulti K _ ((range T).mkQ ∘ z)) = 1) :
    φ γ * T.detLineEndEquiv (exteriorPower.ιMulti K _ u ⊗ₜ ξ) = φ β := by
  rw [← smul_eq_mul, ← map_smul, ← TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul
    (ker T).injective_subtype T.exact_subtype_ker_map T.exact_map_mkQ_range
    (range T).mkQ_surjective u v z hβ hγ φ hξ, detLineEndEquiv_detLineFourTermEquiv]

/-- **The canonical and the bijective trivializations differ by the determinant.** For a bijective
endomorphism `T`, the canonical trivialization of its determinant line is `(det T)⁻¹` times the
trivialization `LinearMap.detLineEquivOfBijective`, which sends the product of the empty exterior
products of kernel and cokernel to `1`. -/
theorem detLineEndEquiv_eq_inv_det_mul (hT : Function.Bijective T) (x : T.detLine) :
    T.detLineEndEquiv x = (LinearMap.det T)⁻¹ * T.detLineEquivOfBijective hT x := by
  have hker := finrank_ker_eq_zero_of_injective hT.1
  have hcoker := finrank_quotient_range_eq_zero_of_surjective hT.2
  have hrange : finrank K (range T) = finrank K V := by
    rw [range_eq_top.mpr hT.2, finrank_top]
  let b := Module.finBasis K V
  let u : Fin (finrank K (ker T)) → ker T := fun i ↦ (Fin.cast hker i).elim0
  let z : Fin (finrank K (V ⧸ range T)) → V := fun i ↦ (Fin.cast hcoker i).elim0
  let ξ : Dual K (TauCeti.detLine K (V ⧸ range T)) := TauCeti.detLineEquivOfFinrankEqZero hcoker
  let φ : Dual K (TauCeti.detLine K V) := b.exteriorPowerTopEquiv
  -- The exterior products of `b` and `T ∘ b` are `β` and `γ` of `detLineEndEquiv_tmul`.
  have key := T.detLineEndEquiv_tmul u (b ∘ Fin.cast hrange) z
    (β := exteriorPower.ιMulti K _ b) (γ := exteriorPower.ιMulti K _ (T ∘ b))
    (by rw [exteriorPower.ιMulti_apply_coe, Fin.append_left_nil _ _ hker,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast, TauCeti.ExteriorAlgebra.ιMulti_comp_cast])
    (by rw [exteriorPower.ιMulti_apply_coe, Fin.append_right_nil _ _ hcoker,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast, ← Function.comp_assoc,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast])
    φ (ξ := ξ) (TauCeti.detLineEquivOfFinrankEqZero_ιMulti hcoker _)
  simp only [φ, LinearEquiv.coe_coe, Module.Basis.exteriorPowerTopEquiv_apply_ιMulti,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one] at key
  have hbij : T.detLineEquivOfBijective hT (exteriorPower.ιMulti K _ u ⊗ₜ ξ) = 1 :=
    (detLineEquivOfBijective_tmul_ιMulti hT u ξ ((range T).mkQ ∘ z)).trans
      (TauCeti.detLineEquivOfFinrankEqZero_ιMulti hcoker _)
  -- The determinant line is a line spanned by `α ⊗ ξ`, on which both sides agree.
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' (exteriorPower.ιMulti K _ u ⊗ₜ ξ)
    fun h ↦ by rw [h, map_zero] at hbij; exact zero_ne_one hbij).mp T.finrank_detLine x
  rw [map_smul, map_smul, hbij, eq_inv_of_mul_eq_one_right key, smul_eq_mul, smul_eq_mul,
    mul_one, mul_comm]

/-- **The canonical and the bijective orientations differ by the sign of the determinant.** Over an
ordered field, for a bijective endomorphism `T`, the sign of the canonical trivialization of its
determinant line is the sign of `det T` times the sign of `LinearMap.detLineEquivOfBijective`. -/
theorem sign_detLineEndEquiv [LinearOrder K] [IsStrictOrderedRing K] (hT : Function.Bijective T)
    (x : T.detLine) :
    SignType.sign (T.detLineEndEquiv x) =
      SignType.sign (LinearMap.det T) * SignType.sign (T.detLineEquivOfBijective hT x) := by
  rw [detLineEndEquiv_eq_inv_det_mul T hT, sign_mul, TauCeti.sign_inv]

end LinearMap
