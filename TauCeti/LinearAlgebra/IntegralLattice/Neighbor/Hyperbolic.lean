/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Neighbor.Isotropic
public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Sum

/-!
# Neighbors become isometric after adding a hyperbolic plane

Let `L` be an even lattice, `p` a positive integer and `v ∈ L` a vector whose norm is divisible
by `2p²`, such that some lattice vector pairs with `v` coprimely to `p`. Then
`L ⊕ U ≅ L.neighbor p v ⊕ U`, where `U` is the hyperbolic plane.

Write `M = L.neighbor p v`, `b = v / p ∈ M` and `e`, `f` for the standard isotropic basis of `U`.
The vector `z = p (b + e - (b · b / 2) f)` of `L ⊕ U` is primitive and isotropic, and its orthogonal
complement modulo `z` is identified with `M` by `x + α e + β f ↦ x - α b`. Choosing `y ∈ L ⊕ U`
with `z · y = 1` and correcting it to an isotropic vector, the plane spanned by `z` and `y` is a
copy of `U` whose orthogonal complement is a copy of `M`. Assembled, this is an explicit rational
isometry of `M ⊕ U` onto `L ⊕ U` carrying the integral carriers onto each other.

In particular two even unimodular lattices that are neighbors become isometric after adding `U`,
although they need not be isometric themselves; this is how cancellation fails over `ℤ`.

## Main results

* `TauCeti.IntegralLattice.nonempty_isometry_orthogonalSum_hyperbolicPlane_neighbor`:
  `L ⊕ U ≅ L.neighbor p v ⊕ U`.

## References

* M. Kneser, *Quadratische Formen*, revised with R. Scharlau, Springer (2002), §28, for
  neighbors.
* J.-P. Serre, *A Course in Arithmetic*, Chapter V, for splitting off hyperbolic planes from
  indefinite unimodular lattices and the resulting failure of cancellation.
-/

public section

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (L : IntegralLattice V)

/-- The isometry of `L.neighbor p v ⊕ U` onto `L ⊕ U`, on the ambient rational spaces. Here `a`
is a vector of `L` with `a · v ≡ 1 (mod p)`; the first coordinate of `U` is the coefficient of `e`
and the second that of `f`. -/
private noncomputable def neighborHyperbolicFwd (p : ℚ) (v a : V) :
    V × (Fin 2 → ℚ) →ₗ[ℚ] V × (Fin 2 → ℚ) where
  toFun X :=
    (X.1 + (X.2 0 - L.form a a / 2 * X.2 1 - L.form X.1 a) • v + X.2 1 • a,
      ![p * (X.2 0 - L.form a a / 2 * X.2 1 - L.form X.1 a),
        -(L.form X.1 v / p) - L.form v v / (2 * p) * (X.2 0 - L.form a a / 2 * X.2 1 -
          L.form X.1 a) + (1 - L.form a v) / p * X.2 1])
  map_add' X Y := by
    ext i
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, LinearMap.add_apply]
      module
    · fin_cases i <;>
        simp only [Prod.snd_add, Pi.add_apply, Prod.fst_add, map_add, LinearMap.add_apply,
          Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        ring
  map_smul' r X := by
    ext i
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      module
    · fin_cases i <;>
        simp only [Prod.smul_snd, Pi.smul_apply, Prod.smul_fst, map_smul, LinearMap.smul_apply,
          smul_eq_mul, RingHom.id_apply, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;>
        ring

/-- The inverse of `neighborHyperbolicFwd`. -/
private noncomputable def neighborHyperbolicBwd (p : ℚ) (v a : V) :
    V × (Fin 2 → ℚ) →ₗ[ℚ] V × (Fin 2 → ℚ) where
  toFun Y :=
    (Y.1 - (Y.2 0 / p) • v - (L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1) • a,
      ![Y.2 0 / p * (1 - L.form a v) + L.form Y.1 a - L.form a a / 2 *
          (L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1),
        L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1])
  map_add' X Y := by
    ext i
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, LinearMap.add_apply]
      module
    · fin_cases i <;>
        simp only [Prod.snd_add, Pi.add_apply, Prod.fst_add, map_add, LinearMap.add_apply,
          Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
        ring
  map_smul' r X := by
    ext i
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      module
    · fin_cases i <;>
        simp only [Prod.smul_snd, Pi.smul_apply, Prod.smul_fst, map_smul, LinearMap.smul_apply,
          smul_eq_mul, RingHom.id_apply, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
          Matrix.cons_val_one] <;>
        ring

private theorem neighborHyperbolicFwd_fst (p : ℚ) (v a : V) (X : V × (Fin 2 → ℚ)) :
    (L.neighborHyperbolicFwd p v a X).1 =
      X.1 + (X.2 0 - L.form a a / 2 * X.2 1 - L.form X.1 a) • v + X.2 1 • a :=
  (rfl)

private theorem neighborHyperbolicFwd_snd_zero (p : ℚ) (v a : V) (X : V × (Fin 2 → ℚ)) :
    (L.neighborHyperbolicFwd p v a X).2 0 = p * (X.2 0 - L.form a a / 2 * X.2 1 - L.form X.1 a) :=
  (rfl)

private theorem neighborHyperbolicFwd_snd_one (p : ℚ) (v a : V) (X : V × (Fin 2 → ℚ)) :
    (L.neighborHyperbolicFwd p v a X).2 1 =
      -(L.form X.1 v / p) - L.form v v / (2 * p) * (X.2 0 - L.form a a / 2 * X.2 1 -
        L.form X.1 a) + (1 - L.form a v) / p * X.2 1 :=
  (rfl)

private theorem neighborHyperbolicBwd_fst (p : ℚ) (v a : V) (Y : V × (Fin 2 → ℚ)) :
    (L.neighborHyperbolicBwd p v a Y).1 =
      Y.1 - (Y.2 0 / p) • v - (L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1) • a :=
  (rfl)

private theorem neighborHyperbolicBwd_snd_zero (p : ℚ) (v a : V) (Y : V × (Fin 2 → ℚ)) :
    (L.neighborHyperbolicBwd p v a Y).2 0 =
      Y.2 0 / p * (1 - L.form a v) + L.form Y.1 a - L.form a a / 2 *
        (L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1) :=
  (rfl)

private theorem neighborHyperbolicBwd_snd_one (p : ℚ) (v a : V) (Y : V × (Fin 2 → ℚ)) :
    (L.neighborHyperbolicBwd p v a Y).2 1 =
      L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1 :=
  (rfl)

private theorem neighborHyperbolicBwd_comp_fwd {p : ℚ} (hp : p ≠ 0) (v a : V) :
    L.neighborHyperbolicBwd p v a ∘ₗ L.neighborHyperbolicFwd p v a = LinearMap.id := by
  refine LinearMap.ext fun X ↦ ?_
  have hva : L.form v a = L.form a v := L.isSymm.eq v a
  ext i
  · simp only [LinearMap.comp_apply, neighborHyperbolicBwd_fst, neighborHyperbolicFwd_fst,
      neighborHyperbolicFwd_snd_zero, neighborHyperbolicFwd_snd_one, map_add, map_smul,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.id_apply]
    match_scalars <;> field_simp <;> ring
  · fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, LinearMap.comp_apply, neighborHyperbolicBwd_snd_zero,
        neighborHyperbolicBwd_snd_one, neighborHyperbolicFwd_fst, neighborHyperbolicFwd_snd_zero,
        neighborHyperbolicFwd_snd_one, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.id_apply, hva] <;>
      field_simp <;> ring

private theorem neighborHyperbolicFwd_comp_bwd {p : ℚ} (hp : p ≠ 0) (v a : V) :
    L.neighborHyperbolicFwd p v a ∘ₗ L.neighborHyperbolicBwd p v a = LinearMap.id := by
  refine LinearMap.ext fun Y ↦ ?_
  have hva : L.form v a = L.form a v := L.isSymm.eq v a
  ext i
  · simp only [LinearMap.comp_apply, neighborHyperbolicFwd_fst, neighborHyperbolicBwd_fst,
      neighborHyperbolicBwd_snd_zero, neighborHyperbolicBwd_snd_one, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.id_apply, hva]
    match_scalars <;> field_simp <;> ring
  · fin_cases i <;>
      simp only [Fin.zero_eta, Fin.mk_one, LinearMap.comp_apply, neighborHyperbolicFwd_snd_zero,
        neighborHyperbolicFwd_snd_one, neighborHyperbolicBwd_fst, neighborHyperbolicBwd_snd_zero,
        neighborHyperbolicBwd_snd_one, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, smul_eq_mul, LinearMap.id_apply, hva] <;>
      field_simp <;> ring

/-- `neighborHyperbolicFwd` preserves the orthogonal sum of `L.form` with the hyperbolic form. -/
private theorem form_neighborHyperbolicFwd {p : ℚ} (hp : p ≠ 0) (v a : V)
    (X Y : V × (Fin 2 → ℚ)) :
    (L.orthogonalSum hyperbolicPlane).form (L.neighborHyperbolicFwd p v a X)
        (L.neighborHyperbolicFwd p v a Y) = (L.orthogonalSum hyperbolicPlane).form X Y := by
  have hva : L.form v a = L.form a v := L.isSymm.eq v a
  have hvY : L.form v Y.1 = L.form Y.1 v := L.isSymm.eq v Y.1
  have haY : L.form a Y.1 = L.form Y.1 a := L.isSymm.eq a Y.1
  simp only [orthogonalSum_form, orthogonalSumForm_apply, hyperbolicPlane_form_apply,
    neighborHyperbolicFwd_fst, neighborHyperbolicFwd_snd_zero, neighborHyperbolicFwd_snd_one,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hva, hvY, haY]
  field_simp
  ring

section Carrier

variable {L} {p : ℕ} [NeZero p] {v : L} (hv : (p : ℤ) ^ 2 ∣ L.integralNorm v) {a : L}
  {c s k : ℤ} (hc : L.form v v = 2 * (p : ℚ) ^ 2 * c) (hs : L.form a a = 2 * s)
  (hk : L.form a v = 1 + p * k)
include hc hs hk

/-- `neighborHyperbolicFwd` maps `L.neighbor p v ⊕ U` into `L ⊕ U`. -/
private theorem neighborHyperbolicFwd_mem {X : V × (Fin 2 → ℚ)}
    (hX : X ∈ ((L.neighbor p v hv).orthogonalSum hyperbolicPlane).carrier) :
    L.neighborHyperbolicFwd p v a X ∈ (L.orthogonalSum hyperbolicPlane).carrier := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [orthogonalSum_carrier, Submodule.mem_prod] at hX
  obtain ⟨hX₁, hX₂⟩ := hX
  rw [mem_hyperbolicPlane_carrier_iff, Fin.forall_fin_two] at hX₂
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ := hX₂
  obtain ⟨y, hy, n, hX₁⟩ := (L.mem_neighbor_carrier_iff hv X.1).mp hX₁
  obtain ⟨y, rfl, m, hm⟩ := (L.mem_neighborKernel_iff p v y).mp hy
  have hya : L.form y a = L.integralForm y a := (L.integralForm_cast y a).symm
  have hyv : L.form y v = p * m := by
    rw [L.isSymm.eq, ← L.integralForm_cast, hm]
    push_cast
    ring
  have hva : L.form v a = L.form a v := L.isSymm.eq v a
  -- The parameter `t` of the construction, multiplied by `p`, is an integer.
  set N : ℤ := p * (z₀ - s * z₁ - L.integralForm y a) - n * (1 + p * k) with hN
  have ht : (p : ℚ) * (X.2 0 - L.form a a / 2 * X.2 1 - L.form X.1 a) = N := by
    rw [← hX₁, ← hz₀, ← hz₁, hs, map_add, LinearMap.add_apply, hya]
    simp only [map_zsmul, map_smul, LinearMap.smul_apply, smul_eq_mul, zsmul_eq_mul, hva, hk, hN]
    push_cast
    field_simp
    ring
  rw [orthogonalSum_carrier, Submodule.mem_prod]
  refine ⟨?_, ?_⟩
  · have h : (L.neighborHyperbolicFwd p v a X).1 =
        ((y + z₁ • a + (z₀ - s * z₁ - L.integralForm y a - n * k) • v : L) : V) := by
      rw [neighborHyperbolicFwd_fst, ← hX₁, ← hz₀, ← hz₁, hs, map_add, LinearMap.add_apply, hya]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Submodule.coe_add,
        Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, hva, hk]
      push_cast
      match_scalars <;> field_simp
      ring
    rw [h]
    exact Submodule.coe_mem _
  · rw [mem_hyperbolicPlane_carrier_iff, Fin.forall_fin_two]
    refine ⟨⟨N, by rw [neighborHyperbolicFwd_snd_zero, ht]⟩,
      ⟨-m - 2 * c * n - c * N - k * z₁, ?_⟩⟩
    have ht' : X.2 0 - L.form a a / 2 * X.2 1 - L.form X.1 a = N / p := by
      rw [← ht]
      field_simp
    have hXv : L.form X.1 v = p * m + 2 * p * c * n := by
      rw [← hX₁, map_add, LinearMap.add_apply, hyv]
      simp only [map_zsmul, map_smul, LinearMap.smul_apply, smul_eq_mul, zsmul_eq_mul, hc]
      field_simp
    rw [neighborHyperbolicFwd_snd_one, ht', hXv, hc, hk, ← hz₁]
    push_cast
    field_simp
    ring

/-- `neighborHyperbolicBwd` maps `L ⊕ U` into `L.neighbor p v ⊕ U`. -/
private theorem neighborHyperbolicBwd_mem {Y : V × (Fin 2 → ℚ)}
    (hY : Y ∈ (L.orthogonalSum hyperbolicPlane).carrier) :
    L.neighborHyperbolicBwd p v a Y ∈
      ((L.neighbor p v hv).orthogonalSum hyperbolicPlane).carrier := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [orthogonalSum_carrier, Submodule.mem_prod] at hY
  obtain ⟨hY₁, hY₂⟩ := hY
  rw [mem_hyperbolicPlane_carrier_iff, Fin.forall_fin_two] at hY₂
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ := hY₂
  set y : L := ⟨Y.1, hY₁⟩
  have hyv : L.form Y.1 v = L.integralForm v y := by
    rw [L.integralForm_cast, L.isSymm.eq]
  have hya : L.form Y.1 a = L.integralForm y a := (L.integralForm_cast y a).symm
  -- The `f`-coordinate of the image is an integer.
  set S : ℤ := L.integralForm v y - p * c * z₀ + p * z₁ with hS
  have hS' : L.form Y.1 v - L.form v v / (2 * p) * Y.2 0 + p * Y.2 1 = S := by
    rw [hyv, hc, ← hz₀, ← hz₁, hS]
    push_cast
    field_simp
  rw [orthogonalSum_carrier, Submodule.mem_prod]
  refine ⟨?_, ?_⟩
  · rw [neighborHyperbolicBwd_fst, hS', mem_neighbor_carrier_iff]
    refine ⟨((y - S • a : L) : V), ?_, -z₀, ?_⟩
    · rw [coe_mem_neighborKernel_iff, map_sub, map_zsmul, smul_eq_mul]
      have hva : L.integralForm v a = 1 + p * k := by
        have h := hk
        rw [L.isSymm.eq, ← L.integralForm_cast] at h
        exact_mod_cast h
      rw [hva, hS]
      exact ⟨-(L.integralForm v y) * k - (z₁ - c * z₀) * (1 + p * k), by ring⟩
    · simp only [Submodule.coe_sub, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, ← hz₀]
      push_cast
      match_scalars <;> field_simp
  · rw [mem_hyperbolicPlane_carrier_iff, Fin.forall_fin_two]
    refine ⟨⟨L.integralForm y a - z₀ * k - s * S, ?_⟩,
      ⟨S, by rw [neighborHyperbolicBwd_snd_one, hS']⟩⟩
    rw [neighborHyperbolicBwd_snd_zero, hS', hya, hs, hk, ← hz₀]
    push_cast
    field_simp
    ring

end Carrier

variable {L} {p : ℕ} [NeZero p] {v : L} (hv : (p : ℤ) ^ 2 ∣ L.integralNorm v)

/-- **Neighbors become isometric after adding a hyperbolic plane.** Let `L` be even and let
`v ∈ L` have norm divisible by `2p²`, with some `w ∈ L` pairing with `v` coprimely to `p`. Then
`L ⊕ U` and `L.neighbor p v ⊕ U` are isometric, where `U` is the hyperbolic plane. -/
theorem nonempty_isometry_orthogonalSum_hyperbolicPlane_neighbor (hL : L.IsEven)
    (hv₂ : 2 * (p : ℤ) ^ 2 ∣ L.integralNorm v) {w : L} (hvw : IsCoprime (L.integralForm v w) p) :
    Nonempty (Isometry (L.orthogonalSum hyperbolicPlane)
      ((L.neighbor p v hv).orthogonalSum hyperbolicPlane)) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  obtain ⟨u, t, hut⟩ := hvw
  obtain ⟨c, hc⟩ := hv₂
  obtain ⟨s, hs⟩ := hL.exists_norm_eq_two_mul (u • w)
  have hc' : L.form v v = 2 * (p : ℚ) ^ 2 * c := by
    rw [← L.integralForm_cast, ← integralNorm_apply, hc]
    push_cast
    ring
  have hs' : L.form (u • w : L) (u • w : L) = 2 * s := by
    rw [← norm_apply]
    exact hs
  have hk : L.form (u • w : L) v = 1 + p * (-t) := by
    rw [L.isSymm.eq, ← L.integralForm_cast, map_zsmul, smul_eq_mul]
    have h := congrArg (Int.cast : ℤ → ℚ) hut
    push_cast at h ⊢
    linear_combination h
  -- The ambient isometry of `L.neighbor p v ⊕ U` onto `L ⊕ U`.
  let e : ((L.neighbor p v hv).orthogonalSum hyperbolicPlane).form.IsometryEquiv
      (L.orthogonalSum hyperbolicPlane).form :=
    { toLinearEquiv := LinearEquiv.ofLinearMap (L.neighborHyperbolicFwd p v (u • w : L))
        (L.neighborHyperbolicBwd p v (u • w : L)) (L.neighborHyperbolicFwd_comp_bwd hp _ _)
        (L.neighborHyperbolicBwd_comp_fwd hp _ _)
      map_app' X Y := (L.form_neighborHyperbolicFwd hp _ _ X Y).trans (by
        simp only [orthogonalSum_form, orthogonalSumForm_apply, neighbor_form]) }
  refine ⟨Isometry.symm ⟨e, le_antisymm ?_ fun Y hY ↦ ?_⟩⟩
  · rintro _ ⟨X, hX, rfl⟩
    exact neighborHyperbolicFwd_mem hv hc' hs' hk hX
  · refine ⟨L.neighborHyperbolicBwd p v (u • w : L) Y,
      neighborHyperbolicBwd_mem hv hc' hs' hk hY, ?_⟩
    exact LinearMap.congr_fun (L.neighborHyperbolicFwd_comp_bwd hp _ _) Y

end TauCeti.IntegralLattice
