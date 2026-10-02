/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Separable
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.DivisorPullback

/-!
# The Weil pairing and the dual isogeny

Let `φ : W₁ → W₂` be a separable isogeny of elliptic curves over a separably closed field `F`, and
`N` a positive integer invertible in `F`. The dual `φ̂ : W₂ → W₁` is adjoint to `φ` for the Weil
pairing (Silverman III.8.2):

    e_N(φ S, T) = e_N(S, φ̂ T)    for `S ∈ W₁[N]` and `T ∈ W₂[N]`,

and consequently `e_N(φ S, φ T) = e_N(S, T) ^ deg φ`.

The proof is Silverman's. Let `g` be a function on `W₂` with divisor `[N]^* (T) - [N]^* (O)`, the
function from which `e_N(·, T)` is built. Over a separably closed field the pullback `φ^* (T)` is
the fibre `∑_{φ P = T} (P)`, a translate of the kernel, so `φ^* ((T) - (O))` is a degree-zero
divisor whose sum is `deg φ • P₀ = φ̂ (φ P₀) = φ̂ T` for any `P₀` over `T`. Hence
`φ^* ((T) - (O)) - ((φ̂ T) - (O))` is the divisor of a function `h`. Since `φ` commutes with `[N]`,
the function `φ^* g / [N]^* h` has divisor `[N]^* (φ̂ T) - [N]^* (O)`, so it computes
`e_N(·, φ̂ T)`. Translation by an `N`-torsion point fixes `[N]^* h`, and moves `φ^* g` to
`φ^* (τ_{φ S}^* g)`, so `e_N(S, φ̂ T) = φ^* (τ_{φ S}^* g / g) = e_N(φ S, T)`.

## Main results

* `TauCeti.Isogeny.exists_principal_eq_divisorPullback_sub`: `φ^* ((T) - (O))` and
  `(φ̂ T) - (O)` differ by a principal divisor.
* `TauCeti.Isogeny.weilPairing_eq_weilPairing_dual`: **`e_N(φ S, T) = e_N(S, φ̂ T)`**.
* `TauCeti.Isogeny.weilPairing_eq_degree_nsmul_weilPairing`: `e_N(φ S, φ T) = e_N(S, T) ^ deg φ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 and III.8.2.
-/

public section

namespace TauCeti.Isogeny

open AlgebraicGeometry WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

local instance : IsIntegrallyClosed W₁.CoordinateRing := W₁.isIntegrallyClosed_coordinateRing
local instance : IsIntegrallyClosed W₂.CoordinateRing := W₂.isIntegrallyClosed_coordinateRing
local instance : IsDedekindDomain W₁.CoordinateRing :=
  W₁.isDedekindDomain_coordinateRing_of_isIntegrallyClosed
local instance : IsDedekindDomain W₂.CoordinateRing :=
  W₂.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **`φ^* ((T) - (O))` is linearly equivalent to `(φ̂ T) - (O)`**: their difference is principal,
over a separably closed field (Silverman III.6.1). Its sum is `deg φ • P₀ - φ̂ T` for any `P₀` over
`T`, and `φ̂ T = φ̂ (φ P₀) = deg φ • P₀`. -/
theorem exists_principal_eq_divisorPullback_sub (T : W₂.Point) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    ∃ h : W₁.FunctionFieldˣ, Divisor.principal W₁.isFunctionField h =
      φ.divisorPullback (fun _ ↦ rfl) (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₂ T).1 -
          WeilDivisor.ofPoint (Place.infinity W₂)) -
        (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₁ ((Hom.ofIsogeny φ.dual).pointMap T)).1 -
          WeilDivisor.ofPoint (Place.infinity W₁)) := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  obtain ⟨P₀, hP₀⟩ := φ.toPointHom_surjective T
  rw [← coe_pointEquivDegreeOnePlace_zero, ← coe_pointEquivDegreeOnePlace_zero,
    ← Point.zero_def, ← Point.zero_def, φ.divisorPullback_ofPoint_sub_eq_sum hP₀]
  set s₀ := (φ.finite_setOf_toPointHom_eq 0).toFinset with hs₀
  let D : (Divisor.degree (k := F) (F := W₁.FunctionField)).ker :=
    ∑ K ∈ s₀, ⟨_, W₁.ofPoint_sub_ofPoint_mem_ker_degree (P₀ + K) K⟩ -
      ⟨_, W₁.ofPoint_sub_ofPoint_mem_ker_degree ((Hom.ofIsogeny φ.dual).pointMap T) 0⟩
  -- the sum of `D` is `#ker φ • P₀ - φ̂ (φ P₀) = deg φ • P₀ - deg φ • P₀`
  have hσ : W₁.divisorSum D = 0 := by
    simp only [D, map_sub, map_sum, divisorSum_ofPoint_sub_ofPoint, add_sub_cancel_right,
      Finset.sum_const, sub_zero]
    rw [hs₀, ← Set.ncard_eq_toFinset_card _ (φ.finite_setOf_toPointHom_eq 0),
      φ.ncard_fiber_toPointHom_eq_degree, ← hP₀,
      ← Hom.pointMap_ofIsogeny_eq_toPointHom, pointMap_dual_pointMap, sub_self]
  obtain ⟨z, hz⟩ := W₁.divisorSum_eq_zero_iff.mp hσ
  exact ⟨z, hz.trans (by simp [D])⟩

/-! ### Adjointness of the dual for the Weil pairing -/

section Pairing

variable (N : ℕ)

omit [DecidableEq F] in
/-- Pulling back along `φ` commutes with pulling back along `[N]`, since `φ ∘ [N] = [N] ∘ φ`. -/
private theorem divisorPullback_divisorPullback_mulByIntIsogeny {hψ₁ : psiFunctionField W₁ N ≠ 0}
    {hψ₂ : psiFunctionField W₂ N ≠ 0} (hN : (N : F) ≠ 0) (D : Divisor F W₂.FunctionField) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    letI := (mulByIntIsogeny W₂ hψ₂).fieldPullback.toRingHom.toAlgebra
    letI := (mulByIntIsogeny W₁ hψ₁).fieldPullback.toRingHom.toAlgebra
    φ.divisorPullback (fun _ ↦ rfl) ((mulByIntIsogeny W₂ hψ₂).divisorPullback (fun _ ↦ rfl) D) =
      (mulByIntIsogeny W₁ hψ₁).divisorPullback (fun _ ↦ rfl)
        (φ.divisorPullback (fun _ ↦ rfl) D) := by
  -- both sides are pullbacks along a composite, and the two composites agree
  have hcomm : φ.comp (mulByIntIsogeny W₁ hψ₁) = (mulByIntIsogeny W₂ hψ₂).comp φ :=
    φ.comp_mulByIntIsogenyOfNeZero (n := N) fun h ↦ hN (by
      rw [Int.natCast_eq_zero.mp h, Nat.cast_zero])
  have hcongr : ∀ ψ ψ' : Isogeny W₁ W₂, ψ = ψ' →
      @divisorPullback _ _ _ _ ψ ψ.fieldPullback.toRingHom.toAlgebra (fun _ ↦ rfl) D =
        @divisorPullback _ _ _ _ ψ' ψ'.fieldPullback.toRingHom.toAlgebra (fun _ ↦ rfl) D := by
    rintro _ _ rfl
    rfl
  -- the composites carry their own algebra structures `F(W₂) → F(W₁)`, of the same type as that of
  -- `φ`, so every structure is passed explicitly
  rw [@divisorPullback_comp _ _ _ _ φ φ.fieldPullback.toRingHom.toAlgebra (fun _ ↦ rfl) _
      (mulByIntIsogeny W₂ hψ₂) (mulByIntIsogeny W₂ hψ₂).fieldPullback.toRingHom.toAlgebra
      ((mulByIntIsogeny W₂ hψ₂).comp φ).fieldPullback.toRingHom.toAlgebra (fun _ ↦ rfl)
      (fun _ ↦ rfl) D,
    @divisorPullback_comp _ _ _ _ (mulByIntIsogeny W₁ hψ₁)
      (mulByIntIsogeny W₁ hψ₁).fieldPullback.toRingHom.toAlgebra (fun _ ↦ rfl) _ φ
      φ.fieldPullback.toRingHom.toAlgebra
      (φ.comp (mulByIntIsogeny W₁ hψ₁)).fieldPullback.toRingHom.toAlgebra (fun _ ↦ rfl)
      (fun _ ↦ rfl) D]
  exact hcongr _ _ hcomm.symm

variable [NeZero N] (hN : (N : F) ≠ 0)

/-- **The dual isogeny is adjoint to `φ` for the Weil pairing**: `e_N(φ S, T) = e_N(S, φ̂ T)` for
`S ∈ W₁[N]` and `T ∈ W₂[N]`, where `φ` is a separable isogeny over a separably closed field in
which `N` is invertible (Silverman III.8.2). The images `φ S` and `φ̂ T` are given as the torsion
points `S'` and `T'`. -/
theorem weilPairing_eq_weilPairing_dual {S : Submodule.torsionBy ℤ W₁.Point (N : ℤ)}
    {T : Submodule.torsionBy ℤ W₂.Point (N : ℤ)} {S' : Submodule.torsionBy ℤ W₂.Point (N : ℤ)}
    {T' : Submodule.torsionBy ℤ W₁.Point (N : ℤ)}
    (hS : (Hom.ofIsogeny φ).pointMap S = S') (hT : (Hom.ofIsogeny φ.dual).pointMap T = T') :
    weilPairing W₂ N hN S' T = weilPairing W₁ N hN S T' := by
  have hchar : ((N : ℤ) : F) ≠ 0 := by rwa [Int.cast_natCast]
  have hψ₁ := psiFunctionField_ne_zero W₁ hchar
  have hψ₂ := psiFunctionField_ne_zero W₂ hchar
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  let _ := (mulByIntIsogeny W₁ hψ₁).fieldPullback.toRingHom.toAlgebra
  let _ := (mulByIntIsogeny W₂ hψ₂).fieldPullback.toRingHom.toAlgebra
  -- `g` computes `e_N(·, T)` on `W₂`, and `div h = φ^* ((T) - (O)) - ((φ̂ T) - (O))` on `W₁`
  obtain ⟨g, hg⟩ := exists_principal_eq_weilPairingDivisor W₂ hchar
    ((Submodule.mem_torsionBy_iff _ _).mp T.2)
  obtain ⟨h, hh⟩ := φ.exists_principal_eq_divisorPullback_sub T
  rw [hT] at hh
  -- `φ^* g / [N]^* h` computes `e_N(·, φ̂ T)` on `W₁`
  let g' : W₁.FunctionFieldˣ := Units.map (φ.fieldPullback : W₂.FunctionField →* _) g *
    (Units.map ((mulByIntIsogeny W₁ hψ₁).fieldPullback : W₁.FunctionField →* _) h)⁻¹
  have hg' : Divisor.principal W₁.isFunctionField g' = weilPairingDivisor W₁ hψ₁ T' := by
    -- the divisor of a pulled-back function is the pulled-back divisor
    have hφg : Divisor.principal W₁.isFunctionField
        (Units.map (φ.fieldPullback : W₂.FunctionField →* _) g) =
          φ.divisorPullback (fun _ ↦ rfl) (Divisor.principal W₂.isFunctionField g) :=
      (divisorPullback_principal φ (fun _ ↦ rfl) g).symm
    have hNh : Divisor.principal W₁.isFunctionField
        (Units.map ((mulByIntIsogeny W₁ hψ₁).fieldPullback : W₁.FunctionField →* _) h) =
          (mulByIntIsogeny W₁ hψ₁).divisorPullback (fun _ ↦ rfl)
            (Divisor.principal W₁.isFunctionField h) :=
      (divisorPullback_principal (mulByIntIsogeny W₁ hψ₁) (fun _ ↦ rfl) h).symm
    rw [Divisor.principal_mul, Divisor.principal_inv, hφg, hNh, hg, hh, weilPairingDivisor_def,
      weilPairingDivisor_def]
    simp only [map_sub, divisorPullback_divisorPullback_mulByIntIsogeny φ N (hψ₁ := hψ₁)
      (hψ₂ := hψ₂) hN]
    abel
  -- translation by `S` fixes `[N]^* h`, since `S` is `N`-torsion
  have hfix : translation W₁ (Point.equivBaseChangeSelf W₁ S)
      ((mulByIntIsogeny W₁ hψ₁).fieldPullback h) = (mulByIntIsogeny W₁ hψ₁).fieldPullback h :=
    mem_ker_iff.mp ((mem_ker_mulByIntIsogeny_iff W₁ hψ₁).mpr (by
      rw [← map_zsmul, (Submodule.mem_torsionBy_iff _ _).mp S.2, map_zero]))
      _ (AlgHom.mem_fieldRange.mpr ⟨h, rfl⟩)
  -- and moves `φ^* g` to `φ^* (τ_{φ S}^* g)`
  have hφS : φ.toPointHom S = S' := by rw [← Hom.pointMap_ofIsogeny_eq_toPointHom, hS]
  have hmove := φ.translation_fieldPullback S g
  rw [hφS] at hmove
  refine Additive.toMul.injective (Subtype.ext (Units.ext ((algebraMap F W₁.FunctionField).injective
    ?_)))
  rw [algebraMap_weilPairing W₁ N hN hg', ← φ.fieldPullback.commutes,
    algebraMap_weilPairing W₂ N hN hg, map_div₀, ← hmove]
  simp only [g', Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, MonoidHom.coe_ofClass,
    map_mul, map_inv₀, hfix]
  field_simp

/-- **A separable isogeny scales the Weil pairing by its degree**:
`e_N(φ S, φ T) = e_N(S, T) ^ deg φ` for `S, T ∈ W₁[N]`, written additively, since
`φ̂ (φ T) = deg φ • T` (Silverman III.8.2). The images `φ S` and `φ T` are given as the torsion
points `S'` and `T'`. -/
theorem weilPairing_eq_degree_nsmul_weilPairing {S T : Submodule.torsionBy ℤ W₁.Point (N : ℤ)}
    {S' T' : Submodule.torsionBy ℤ W₂.Point (N : ℤ)} (hS : (Hom.ofIsogeny φ).pointMap S = S')
    (hT : (Hom.ofIsogeny φ).pointMap T = T') :
    weilPairing W₂ N hN S' T' = φ.degree • weilPairing W₁ N hN S T := by
  rw [φ.weilPairing_eq_weilPairing_dual N hN hS (T' := φ.degree • T)
    (by rw [← hT, pointMap_dual_pointMap, Submodule.coe_smul_of_tower]), map_nsmul]

end Pairing

end TauCeti.Isogeny

end
