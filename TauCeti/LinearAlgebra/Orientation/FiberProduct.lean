/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.ShortExact
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.Ray

/-!
# Orientations of transverse fibre products of vector spaces

Let `α : X → T` and `β : Y → T` be linear maps of finite-dimensional vector spaces over a linearly
ordered field which are *transverse*: the map `(ξ, η) ↦ α ξ - β η` from `X × Y` onto `T` is
surjective. Its kernel `Q = {(ξ, η) | α ξ = β η}` is the *fibre product* of `α` and `β`, and the
short exact sequence

`0 → Q → X × Y → T → 0`

relates the dimensions by `dim Q + dim T = dim X + dim Y`. This is the tangent-space model of a
transverse fibre product of manifolds `X ×_T Y`, such as the space of broken trajectories
`𝓜(C, E) ×_E 𝓜(E, D)` in Morse–Bott homology, or a transverse intersection of submanifolds.

Orientations of `X`, `Y` and `T` orient `Q` (`Orientation.fiberProduct`) by the convention

`[X][Y] = (-1) ^ (dim Y · dim T) [Q][T]`,

where `[X][Y]` is the product orientation of `X × Y` (`Orientation.prod`) and `[Q][T]` is the
subspace-first orientation of the short exact sequence (`Orientation.shortExact`)
(`Orientation.shortExact_fiberProduct`). Informally, `[Q]` is the formal product `[X][T]^∨[Y]`:
the base `T` is cancelled against the first factor. When `T = 0` the sign is trivial and
`Q = X × Y`.

Exchanging the factors carries the fibre product of `α` and `β` to that of `β` and `α`. On
orientations this costs the sign `(-1) ^ (dim X · dim Y + dim T · (dim X + dim Y) + dim T)`
(`Orientation.map_fiberProduct_comm`): the exchange of `X` and `Y` contributes `dim X · dim Y`,
the two conventions contribute `dim T · (dim X + dim Y)`, and the quotient map
`(ξ, η) ↦ α ξ - β η` changes sign, which reverses `T` and contributes `dim T`.

## Main definitions

* `Orientation.fiberProduct`: the orientation of the fibre product of two transverse maps.

## Main results

* `Orientation.shortExact_fiberProduct`: the defining identity
  `[X][Y] = (-1) ^ (dim Y · dim T) [Q][T]`.
* `Orientation.fiberProduct_eq_iff`: the fibre product orientation is the unique orientation
  satisfying that identity.
* `Orientation.map_fiberProduct_comm`: the sign of exchanging the factors of a fibre product.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (fibre products of Morse–Bott trajectory spaces
  over critical submanifolds and their orientations).
-/

public section
noncomputable section

open Module

variable {K X Y T : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup T] [Module K T]

namespace LinearMap

variable (α : X →ₗ[K] T) (β : Y →ₗ[K] T)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Precomposing `(η, ξ) ↦ β η - α ξ` with the exchange of factors gives the negative of
`(ξ, η) ↦ α ξ - β η`. -/
theorem coprod_neg_comp_prodComm :
    β.coprod (-α) ∘ₗ (LinearEquiv.prodComm K X Y).toLinearMap = -α.coprod (-β) := by
  rw [coprod_comp_prodComm]
  ext <;> simp

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The exchange of factors carries the fibre product of `α` and `β` onto that of `β` and `α`. -/
theorem map_prodComm_ker_coprod_neg :
    (ker (α.coprod (-β))).map (LinearEquiv.prodComm K X Y : X × Y →ₗ[K] Y × X) =
      ker (β.coprod (-α)) := by
  rw [Submodule.map_equiv_eq_comap_symm, ← ker_comp]
  ext z
  simp only [mem_ker, coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  have h := LinearMap.congr_fun (coprod_neg_comp_prodComm β α) z
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.neg_apply] at h
  rw [show (LinearEquiv.prodComm K X Y).symm z = LinearEquiv.prodComm K Y X z from rfl, h,
    neg_eq_zero]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Transversality of `α` and `β` is symmetric. -/
theorem surjective_coprod_neg_comm (h : Function.Surjective (α.coprod (-β))) :
    Function.Surjective (β.coprod (-α)) := by
  intro z
  obtain ⟨w, hw⟩ := h (-z)
  refine ⟨LinearEquiv.prodComm K X Y w, ?_⟩
  have hw' := LinearMap.congr_fun (coprod_neg_comp_prodComm α β) w
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.neg_apply] at hw'
  rw [hw', hw, neg_neg]

end LinearMap

namespace Orientation

variable [FiniteDimensional K X] [FiniteDimensional K Y] [FiniteDimensional K T]
  {α : X →ₗ[K] T} {β : Y →ₗ[K] T} {x y t q : ℕ}

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K T] in
/-- For transverse `α` and `β`, the fibre product has dimension `dim X + dim Y - dim T`. -/
private theorem finrank_ker_coprod_neg (h : Function.Surjective (α.coprod (-β)))
    (hx : finrank K X = x) (hy : finrank K Y = y) (ht : finrank K T = t) (hq : q + t = x + y) :
    finrank K (LinearMap.ker (α.coprod (-β))) = q := by
  have hrank := (LinearMap.exact_subtype_ker_map (α.coprod (-β))).finrank_eq_add
    (Submodule.injective_subtype _) h
  rw [Module.finrank_prod, hx, hy, ht] at hrank
  omega

/-- The orientation of the fibre product `Q = {(ξ, η) | α ξ = β η}` of two transverse linear maps
`α : X → T` and `β : Y → T`, induced by orientations of `X`, `Y` and `T` through the convention
`[X][Y] = (-1) ^ (dim Y · dim T) [Q][T]` for the short exact sequence
`0 → Q → X × Y → T → 0` with quotient map `(ξ, η) ↦ α ξ - β η`
(`Orientation.shortExact_fiberProduct`). -/
def fiberProduct (h : Function.Surjective (α.coprod (-β))) (ox : Orientation K X (Fin x))
    (oy : Orientation K Y (Fin y)) (ot : Orientation K T (Fin t)) (hx : finrank K X = x)
    (hy : finrank K Y = y) (ht : finrank K T = t) (hq : q + t = x + y) :
    Orientation K (LinearMap.ker (α.coprod (-β))) (Fin q) :=
  shortExactLeft (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) h
    (finrank_ker_coprod_neg h hx hy ht hq) ht
    (reindex K (X × Y) (finCongr hq.symm) ((-1 : Kˣ) ^ (y * t) • prod ox oy hx hy)) ot

variable (h : Function.Surjective (α.coprod (-β))) (ox : Orientation K X (Fin x))
  (oy : Orientation K Y (Fin y)) (ot : Orientation K T (Fin t)) (hx : finrank K X = x)
  (hy : finrank K Y = y) (ht : finrank K T = t) (hq : q + t = x + y)

/-- The defining identity of the fibre product orientation,
`[X][Y] = (-1) ^ (dim Y · dim T) [Q][T]`, where `[Q][T]` is the subspace-first orientation of
`0 → Q → X × Y → T → 0`. -/
@[simp]
theorem shortExact_fiberProduct (hQ : finrank K (LinearMap.ker (α.coprod (-β))) = q) :
    shortExact (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) h
        (fiberProduct h ox oy ot hx hy ht hq) ot hQ ht =
      reindex K (X × Y) (finCongr hq.symm) ((-1 : Kˣ) ^ (y * t) • prod ox oy hx hy) :=
  shortExact_shortExactLeft _ _ h _ ht _ ot

/-- The fibre product orientation is the unique orientation `oq` of `Q` with
`[X][Y] = (-1) ^ (dim Y · dim T) [oq][T]`. -/
theorem fiberProduct_eq_iff (hQ : finrank K (LinearMap.ker (α.coprod (-β))) = q)
    (oq : Orientation K (LinearMap.ker (α.coprod (-β))) (Fin q)) :
    fiberProduct h ox oy ot hx hy ht hq = oq ↔
      shortExact (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) h oq ot hQ
          ht =
        reindex K (X × Y) (finCongr hq.symm) ((-1 : Kˣ) ^ (y * t) • prod ox oy hx hy) :=
  shortExactLeft_eq_iff _ _ h hQ ht _ ot oq

/-- Reversing the orientation of the first factor reverses the fibre product orientation. -/
@[simp]
theorem fiberProduct_neg_left :
    fiberProduct h (-ox) oy ot hx hy ht hq = -fiberProduct h ox oy ot hx hy ht hq := by
  simp only [fiberProduct, prod_neg_left, Module.Ray.units_smul_neg, Orientation.reindex_neg,
    shortExactLeft_neg_left]

/-- Reversing the orientation of the second factor reverses the fibre product orientation. -/
@[simp]
theorem fiberProduct_neg_right :
    fiberProduct h ox (-oy) ot hx hy ht hq = -fiberProduct h ox oy ot hx hy ht hq := by
  simp only [fiberProduct, prod_neg_right, Module.Ray.units_smul_neg, Orientation.reindex_neg,
    shortExactLeft_neg_left]

/-- Reversing the orientation of the base reverses the fibre product orientation. -/
@[simp]
theorem fiberProduct_neg_base :
    fiberProduct h ox oy (-ot) hx hy ht hq = -fiberProduct h ox oy ot hx hy ht hq := by
  simp only [fiberProduct, shortExactLeft_neg_right]

/-- Exchanging the factors of a fibre product: the exchange `X × Y ≃ Y × X` restricts to an
isomorphism of the fibre product of `α` and `β` with that of `β` and `α`, and it carries the fibre
product orientation of `ox`, `oy` to `(-1) ^ (dim X · dim Y + dim T · (dim X + dim Y) + dim T)`
times that of `oy`, `ox`. -/
theorem map_fiberProduct_comm :
    map (Fin q) ((LinearEquiv.prodComm K X Y).ofSubmodules _ _
        (LinearMap.map_prodComm_ker_coprod_neg α β)) (fiberProduct h ox oy ot hx hy ht hq) =
      (-1 : Kˣ) ^ (x * y + t * (x + y) + t) •
        fiberProduct (LinearMap.surjective_coprod_neg_comm α β h) oy ox ot hy hx ht
          (hq.trans (add_comm x y)) := by
  set h' := LinearMap.surjective_coprod_neg_comm α β h
  set σ := (LinearEquiv.prodComm K X Y).ofSubmodules _ _ (LinearMap.map_prodComm_ker_coprod_neg α β)
  have hQ := finrank_ker_coprod_neg h hx hy ht hq
  have hQ' : finrank K (LinearMap.ker (β.coprod (-α))) = q :=
    finrank_ker_coprod_neg h' hy hx ht (hq.trans (add_comm x y))
  set oq := fiberProduct h ox oy ot hx hy ht hq
  set oq' := fiberProduct h' oy ox ot hy hx ht (hq.trans (add_comm x y))
  -- Naturality of the subspace-first orientation along the exchange of factors, which restricts
  -- to `σ` on the fibre products and induces the negation of `T` on the quotients.
  have hnat := map_shortExact (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _)
    h hQ ht (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) h' σ
    (LinearEquiv.prodComm K X Y) (LinearEquiv.neg K) (by ext <;> rfl)
    (by rw [LinearMap.coprod_neg_comp_prodComm]; ext <;> simp) oq ot
  have hfin : (finCongr (add_comm y x)).trans (finCongr hq.symm) =
      finCongr (hq.trans (add_comm x y)).symm := by
    ext; simp
  have hneg : map (Fin t) (LinearEquiv.neg K) ot = (-1 : Kˣ) ^ t • ot := by
    rw [map_linearEquiv_neg ot (by rw [Fintype.card_fin, ht]), ht]
  rw [shortExact_fiberProduct, hneg, shortExact_units_smul_right,
    map_reindex, map_units_smul, map_prodComm_prod, smul_smul, reindex_units_smul,
    ← reindex_trans, hfin] at hnat
  -- The left side of `hnat` is now expressed through the product orientation of `oy` and `ox`,
  -- which the defining identity of `oq'` relates to `oq'`.
  have hdef := shortExact_fiberProduct h' oy ox ot hy hx ht (hq.trans (add_comm x y)) hQ'
  rw [reindex_units_smul] at hdef
  have hinv (v : Orientation K (Y × X) (Fin (q + t))) : (-1 : Kˣ) ^ t • (-1 : Kˣ) ^ t • v = v := by
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  rw [← (shortExact_inj_left (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) h'
    hQ' ht ot), shortExact_units_smul_left, hdef,
    ← hinv (shortExact _ _ h' (map (Fin q) σ oq) ot _ ht), ← hnat]
  simp only [smul_smul, ← pow_add]
  -- The two exponents differ by the even number `2 * (x * t)`.
  congr 1
  rw [show x * y + t * (x + y) + t + x * t = t + (y * t + x * y) + 2 * (x * t) by ring,
    pow_add _ _ (2 * (x * t)), pow_mul, neg_one_sq, one_pow, mul_one]

end Orientation
