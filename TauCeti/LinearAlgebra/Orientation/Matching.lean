/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.LinearMapSign
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# The sign of the matching map of two constraints

Let `a : U → V` and `b : S → V` be linear maps. The **matching map** of `a` and `b`
(`LinearMap.matchingMap a b`) is

`U × V × S → V × V`, `(u, v, s) ↦ (a u - v, v - b s)`.

It compares a point `v` of `V` with a point of `U` and a point of `S` through the two constraints
`a u = v` and `v = b s`, in this order. Its kernel is the set of triples with `a u = v = b s`
(`LinearMap.mem_ker_matchingMap_iff`), and it is an isomorphism exactly when `a` and `b` are
injective and `V` is the direct sum of their images, that is, when `a.coprod b : U × S → V` is an
isomorphism (`LinearMap.bijective_matchingMap_iff`).

Over a linearly ordered field, for orientations of finite-dimensional `U`, `S` and `V`, of
dimensions `k`, `l` and `k + l`, the sign of the matching
map, from the product orientation `[U][V][S]` to `[V][V]`, is `(-1) ^ (k l)` times the sign of
`a.coprod b`, from `[U][S]` to `[V]` (`Orientation.linearMapSign_matchingMap`). When `V` is
even-dimensional, `k l` has the parity of `k`, so the sign is `(-1) ^ k` times that of
`a.coprod b` (`Orientation.linearMapSign_matchingMap_of_even`).

This is the linear algebra of the constant-core face of the Morse inverse family of the
Piunikhin–Salamon–Schwarz maps. There a constant map at a critical point `p` of a Morse function
on a symplectic manifold of dimension `2n` meets the unstable manifold of `p` at one pole and the
stable manifold of `p` at the other. The linearized constraints are the matching map of the
inclusions of the unstable tangent space `U = T_p W^u(p)`, of dimension `k = ind(p)`, and the
stable tangent space `S = T_p W^s(p)` into `V = T_p X`. These are complementary, so when `V` is
oriented as `[U][S]` the matching map of the constant core has sign `(-1) ^ k`, in every index `k`.
The stable-first orientation `[S][U]` of `V` differs from `[U][S]` by the same sign `(-1) ^ (k l)`
(`Orientation.map_prodComm_prod`).

## Main definitions

* `LinearMap.matchingMap a b`: the map `(u, v, s) ↦ (a u - v, v - b s)`.

## Main results

* `LinearMap.bijective_matchingMap_iff`: the matching map is an isomorphism exactly when
  `a.coprod b` is.
* `Orientation.map_matchingMap`: if `e : U × S ≃ V` carries `[U][S]` to `[V]`, the matching map
  of the restrictions of `e` to `U` and `S` carries `[U][V][S]` to `(-1) ^ (k l) [V][V]`.
* `Orientation.linearMapSign_matchingMap`: the sign of the matching map is `(-1) ^ (k l)` times
  the sign of `a.coprod b`, whether or not they are isomorphisms.
* `Orientation.linearMapSign_matchingMap_of_even`: for even-dimensional `V`, the sign is
  `(-1) ^ k` times the sign of `a.coprod b`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, §4,
  for the Morse inverse of the PSS maps and its constant-map end.
-/

public section

open Function Module

variable {U S V : Type*} [AddCommGroup U] [AddCommGroup S] [AddCommGroup V]

namespace LinearMap

variable {R : Type*} [Semiring R] [Module R U] [Module R S] [Module R V]

/-- The **matching map** `(u, v, s) ↦ (a u - v, v - b s)` of two linear maps `a : U → V` and
`b : S → V`. It compares a point `v` of `V` with a point of `U` and a point of `S` through the
constraints `a u = v` and `v = b s`, in this order. -/
def matchingMap (a : U →ₗ[R] V) (b : S →ₗ[R] V) : U × V × S →ₗ[R] V × V :=
  (a ∘ₗ fst R U (V × S) - fst R V S ∘ₗ snd R U (V × S)).prod
    (fst R V S ∘ₗ snd R U (V × S) - b ∘ₗ snd R V S ∘ₗ snd R U (V × S))

@[simp]
theorem matchingMap_apply (a : U →ₗ[R] V) (b : S →ₗ[R] V) (x : U × V × S) :
    matchingMap a b x = (a x.1 - x.2.1, x.2.1 - b x.2.2) :=
  (rfl)

/-- The kernel of the matching map consists of the triples `(u, v, s)` with `a u = v = b s`. -/
theorem mem_ker_matchingMap_iff (a : U →ₗ[R] V) (b : S →ₗ[R] V) (x : U × V × S) :
    x ∈ ker (matchingMap a b) ↔ a x.1 = x.2.1 ∧ x.2.1 = b x.2.2 := by
  simp [sub_eq_zero]

/-- The matching map of `a` and `b` is an isomorphism exactly when `a.coprod b : U × S → V` is:
when `V` is the direct sum of the images of `a` and `b`, and both are injective. -/
theorem bijective_matchingMap_iff (a : U →ₗ[R] V) (b : S →ₗ[R] V) :
    Bijective (matchingMap a b) ↔ Bijective (a.coprod b) := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun w ↦ ?_⟩
    · -- A zero `(u, s)` of `a.coprod b` gives the zero `(u, a u, -s)` of the matching map.
      have h := @hinj (x.1, a x.1, -x.2) 0 (by
        simp only [coprod_apply] at hx
        simp [map_neg, eq_neg_of_add_eq_zero_left hx])
      simp only [Prod.mk_eq_zero, neg_eq_zero] at h
      exact Prod.ext h.1 h.2.2
    · -- A preimage `(u, v, s)` of `(0, w)` gives the preimage `(u, -s)` of `w`.
      obtain ⟨x, hx⟩ := hsurj (0, w)
      simp only [matchingMap_apply, Prod.mk.injEq, sub_eq_zero] at hx
      exact ⟨(x.1, -x.2.2), by simp [hx.1, ← hx.2, sub_eq_add_neg]⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
    · -- A zero `(u, v, s)` of the matching map gives the zero `(u, -s)` of `a.coprod b`.
      simp only [matchingMap_apply, Prod.mk_eq_zero, sub_eq_zero] at hx
      have h := @hinj (x.1, -x.2.2) 0 (by simp [hx.1, hx.2])
      simp only [Prod.mk_eq_zero, neg_eq_zero] at h
      have hv : x.2.1 = 0 := by rw [← hx.1, h.1, map_zero]
      exact Prod.ext h.1 (Prod.ext hv h.2)
    · -- A preimage `(u, s')` of `y.1 + y.2` gives the preimage `(u, a u - y.1, -s')`.
      obtain ⟨z, hz⟩ := hsurj (y.1 + y.2)
      simp only [coprod_apply] at hz
      refine ⟨(z.1, a z.1 - y.1, -z.2), Prod.ext ?_ ?_⟩
      · simp
      · simp only [matchingMap_apply, map_neg, sub_neg_eq_add]
        rw [sub_add_eq_add_sub, hz]
        abel

end LinearMap

namespace Orientation

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Module K U] [Module K S]
  [Module K V] [FiniteDimensional K U] [FiniteDimensional K S] [FiniteDimensional K V] {k l : ℕ}

/-- **The matching map carries `[U][V][S]` to `(-1) ^ (k l) [V][V]`.** Let `e : U × S ≃ V` be a
linear equivalence carrying the product orientation `[U][S]` of orientations of dimensions `k` and
`l` to an orientation `oV`, and let `M` be a linear equivalence agreeing with the matching map
`(u, v, s) ↦ (e (u, 0) - v, v - e (0, s))`. Then `M` carries `[U][V][S]` to `(-1) ^ (k l)` times
`[V][V]`. -/
theorem map_matchingMap (oU : Orientation K U (Fin k)) (oS : Orientation K S (Fin l))
    (oV : Orientation K V (Fin (k + l))) (hU : finrank K U = k) (hS : finrank K S = l)
    (hV : finrank K V = k + l) (e : (U × S) ≃ₗ[K] V)
    (he : Orientation.map (Fin (k + l)) e (prod oU oS hU hS) = oV) (M : (U × V × S) ≃ₗ[K] V × V)
    (hM : ∀ x, M x = LinearMap.matchingMap (e.toLinearMap ∘ₗ LinearMap.inl K U S)
      (e.toLinearMap ∘ₗ LinearMap.inr K U S) x) :
    Orientation.map (Fin (k + (k + l + l))) M
        (prod oU (prod oV oS hV hS) hU (by rw [finrank_prod, hV, hS])) =
      (-1 : Kˣ) ^ (k * l) • Orientation.reindex K (V × V) (finCongr (by omega))
        (prod oV oV hV hV) := by
  set a := e.toLinearMap ∘ₗ LinearMap.inl K U S
  -- The shear `(u, v, s) ↦ (u, v - a u, s)` of `U × (V × S)`.
  let T₁ : (U × V × S) ≃ₗ[K] U × V × S := (LinearEquiv.refl K U).skewProd
    (LinearEquiv.refl K (V × S)) (-(LinearMap.inl K V S ∘ₗ a))
  -- The reordering `(u, w, s) ↦ (w, u, s)`.
  let R : (U × V × S) ≃ₗ[K] V × U × S :=
    ((LinearEquiv.prodAssoc K U V S).symm.trans
      ((LinearEquiv.prodComm K U V).prodCongr (LinearEquiv.refl K S))).trans
      (LinearEquiv.prodAssoc K V U S)
  -- The map `(w, u, s) ↦ (-w, e (u, -s))`.
  let P : (V × U × S) ≃ₗ[K] V × V := (LinearEquiv.neg K).prodCongr
    (((LinearEquiv.refl K U).prodCongr (LinearEquiv.neg K)).trans e)
  -- The shear `(x, y) ↦ (x, y - x)` of `V × V`.
  let T₂ : (V × V) ≃ₗ[K] V × V :=
    (LinearEquiv.refl K V).skewProd (LinearEquiv.refl K V) (-LinearMap.id)
  have hfac : M = ((T₁.trans R).trans P).trans T₂ := by
    refine LinearEquiv.ext fun ⟨u, v, s⟩ ↦ ?_
    rw [hM]
    have h₁ : e (u, -s) = e (u, 0) - e (0, s) := by
      rw [← map_sub, Prod.mk_sub_mk, sub_zero, zero_sub]
    refine Prod.ext ?_ ?_ <;> simp [T₁, R, P, T₂, a, h₁] <;> module
  have hT₁ := map_skewProd_refl (-(LinearMap.inl K V S ∘ₗ a))
    (prod oU (prod oV oS hV hS) hU (by rw [finrank_prod, hV, hS]))
    (by rw [Fintype.card_fin, finrank_prod, finrank_prod, hU, hV, hS])
  have hnV : Orientation.map (Fin (k + l)) (LinearEquiv.neg K) oV = (-1 : Kˣ) ^ (k + l) • oV := by
    rw [map_linearEquiv_neg oV (by rw [Fintype.card_fin, hV]), hV]
  have hnS : Orientation.map (Fin l) (LinearEquiv.neg K) oS = (-1 : Kˣ) ^ l • oS := by
    rw [map_linearEquiv_neg oS (by rw [Fintype.card_fin, hS]), hS]
  have hP : Orientation.map (Fin (k + l + (k + l))) P (prod oV (prod oU oS hU hS) hV
      (by rw [finrank_prod, hU, hS])) =
      ((-1 : Kˣ) ^ (k + l) * (-1 : Kˣ) ^ l) • prod oV oV hV hV := by
    rw [map_prod, map_trans, map_prod, map_refl, Equiv.refl_apply, hnV, hnS,
      prod_units_smul_right, map_units_smul, he, prod_units_smul_left, prod_units_smul_right,
      smul_smul]
  have hT₂ := map_skewProd_refl (-LinearMap.id : V →ₗ[K] V)
    (Orientation.reindex K (V × V) (finCongr (by omega)) (prod oV oV hV hV) :
      Orientation K (V × V) (Fin (k + (k + l + l))))
    (by rw [Fintype.card_fin, finrank_prod, hV]; omega)
  rw [hfac, map_trans, map_trans, map_trans, hT₁,
    map_prodAssoc_symm_trans_prodComm_prod oU oV oS hU hV hS, map_units_smul, map_reindex, hP,
    reindex_units_smul, map_units_smul, map_units_smul, hT₂, smul_smul, ← mul_assoc]
  congr 1
  -- The exponents `k (k + l) + (k + l) + l` and `k l` have the same parity.
  rw [← pow_add, ← pow_add, show k * (k + l) + (k + l) + l = k * l + (k * (k + 1) + 2 * l) by ring,
    pow_add, pow_add, (Nat.even_mul_succ_self k).neg_one_pow, (even_two_mul l).neg_one_pow, one_mul,
    mul_one]

/-- **The sign of the matching map.** For orientations `oU`, `oS` and `oV` of dimensions `k`, `l`
and `k + l`, the sign of the matching map `(u, v, s) ↦ (a u - v, v - b s)`, from the product
orientation `[U][V][S]` to `[V][V]`, is `(-1) ^ (k l)` times the sign of
`a.coprod b : U × S → V`, from `[U][S]` to `[V]`. Both signs are `0` when the maps are not
isomorphisms (`LinearMap.bijective_matchingMap_iff`). -/
theorem linearMapSign_matchingMap (oU : Orientation K U (Fin k)) (oS : Orientation K S (Fin l))
    (oV : Orientation K V (Fin (k + l))) (hU : finrank K U = k) (hS : finrank K S = l)
    (hV : finrank K V = k + l) (a : U →ₗ[K] V) (b : S →ₗ[K] V) :
    linearMapSign (prod oU (prod oV oS hV hS) hU (by rw [finrank_prod, hV, hS]))
        (Orientation.reindex K (V × V) (finCongr (by omega)) (prod oV oV hV hV))
        (LinearMap.matchingMap a b) =
      (-1) ^ (k * l) * linearMapSign (prod oU oS hU hS) oV (a.coprod b) := by
  by_cases h : Bijective (a.coprod b)
  · obtain ⟨u, hu, hmap⟩ := exists_linearMapSign_eq_and_map_eq (o := prod oU oS hU hS) (o' := oV)
      (by rw [Fintype.card_fin, hV]) h
    set w : Kˣ := Units.map (Int.castRingHom K).toMonoidHom u
    have hw : w * w = 1 := by
      rcases Int.units_eq_one_or u with rfl | rfl <;> ext <;> simp [w]
    have hM := (LinearMap.bijective_matchingMap_iff a b).2 h
    have key := map_matchingMap oU oS (w • oV) hU hS hV (LinearEquiv.ofBijective _ h) hmap
      (LinearEquiv.ofBijective _ hM) fun _ ↦ by simp
    rw [prod_units_smul_left, prod_units_smul_right, map_units_smul, prod_units_smul_left,
      prod_units_smul_right, smul_smul, hw, one_smul] at key
    -- Since `w * w = 1`, the matching map carries `[U][V][S]` to `(-1) ^ (k l) w [V][V]`.
    have key' : Orientation.map _ (LinearEquiv.ofBijective _ hM)
        (prod oU (prod oV oS hV hS) hU (by rw [finrank_prod, hV, hS])) =
        ((-1) ^ (k * l) * w) • Orientation.reindex K (V × V) (finCongr (by omega))
          (prod oV oV hV hV) := by
      rw [← smul_left_cancel_iff w, key, smul_smul, mul_left_comm, hw, mul_one]
    rw [linearMapSign_eq_of_map_eq (L := LinearMap.matchingMap a b)
      (LinearEquiv.ofBijective _ hM) (fun _ ↦ rfl) (u := (-1) ^ (k * l) * u)
      (by rw [key']; congr 1; ext; simp [w]), hu, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_neg, Units.val_one]
  · rw [linearMapSign_of_not_bijective h, linearMapSign_of_not_bijective
      (mt (LinearMap.bijective_matchingMap_iff a b).1 h), mul_zero]

/-- **The sign of the matching map in even dimension.** When `V` has even dimension `k + l`, the
sign of the matching map `(u, v, s) ↦ (a u - v, v - b s)`, from `[U][V][S]` to `[V][V]`, is
`(-1) ^ k` times the sign of `a.coprod b`, from `[U][S]` to `[V]`: then `k l` has the parity of
`k`. For complementary unstable and stable tangent spaces of a Morse critical point of index `k`
in a symplectic manifold, oriented as `[V] = [U][S]`, this is the sign `(-1) ^ k` of the
constant-core face, in every index `k`. -/
theorem linearMapSign_matchingMap_of_even (oU : Orientation K U (Fin k))
    (oS : Orientation K S (Fin l)) (oV : Orientation K V (Fin (k + l))) (hU : finrank K U = k)
    (hS : finrank K S = l) (hV : finrank K V = k + l) (a : U →ₗ[K] V) (b : S →ₗ[K] V)
    (hkl : Even (k + l)) :
    linearMapSign (prod oU (prod oV oS hV hS) hU (by rw [finrank_prod, hV, hS]))
        (Orientation.reindex K (V × V) (finCongr (by omega)) (prod oV oV hV hV))
        (LinearMap.matchingMap a b) =
      (-1) ^ k * linearMapSign (prod oU oS hU hS) oV (a.coprod b) := by
  rw [linearMapSign_matchingMap]
  congr 1
  rcases Nat.even_or_odd k with hk | hk
  · rw [(hk.mul_right l).neg_one_pow, hk.neg_one_pow]
  · have hl : Odd l := by
      obtain ⟨r, hr⟩ := hkl
      obtain ⟨t, ht⟩ := hk
      exact ⟨r - t - 1, by omega⟩
    rw [(hk.mul hl).neg_one_pow, hk.neg_one_pow]

end Orientation
