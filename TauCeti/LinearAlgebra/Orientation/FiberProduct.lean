/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Orientation.ShortExact
public import TauCeti.LinearAlgebra.Orientation.Transverse
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

Iterated fibre products are associative with no sign (`Orientation.map_fiberProduct_assoc`): for
further maps `γ : Y → S` and `δ : Z → S`, the reassociation
`(X ×_T Y) ×_S Z ≃ X ×_T (Y ×_S Z)` (`LinearMap.fiberProductAssoc`) carries the orientation
built from `X ×_T Y` and `Z` to the one built from `X` and `Y ×_S Z`, as the formal products
`([X][T]^∨[Y])[S]^∨[Z]` and `[X][T]^∨([Y][S]^∨[Z])` suggest. Both fibre products sit in
`X × Y × Z` as the kernel of `(ξ, η, ζ) ↦ (α ξ - β η, γ η - δ ζ)`, cut out by the two
conditions in opposite orders; exchanging them costs `(-1) ^ (dim S · dim T)`, which cancels
against the signs of the two conventions. This is the linear input for orienting iterated broken
strata `𝓜(C, E) ×_E 𝓜(E, F) ×_F 𝓜(F, D)` in Morse–Bott homology independently of bracketing.

The boundary of a fibre product is oriented by the formula

`∂(X ×_T Y) = (∂X) ×_T Y + (-1) ^ (dim X + dim T) X ×_T ∂Y`

for the outward-first boundary orientation `Orientation.transverse`. In the linear model, a
boundary of `X` is a hyperplane `p` of `X`, and the corresponding boundary of the fibre product is
the fibre product of `α ∘ p.subtype` and `β`, a hyperplane of `X ×_T Y` through the inclusion
`LinearMap.fiberProductInclusionLeft`. For an outward vector `v` of the fibre product, the induced
orientation of this hyperplane is the fibre product orientation for the boundary orientation of
`p` induced by `v.1` (`Orientation.transverse_fiberProduct_left`). Along a hyperplane of `Y` the
same holds up to the sign `(-1) ^ (dim X + dim T)` (`Orientation.transverse_fiberProduct_right`):
the outward vector moves past `X`, contributing `dim X`, and the factor `[Y]` in the defining
identity drops one dimension, contributing `dim T`. This is the linear input for the signs of the
codimension-one faces of compactified spaces of Morse–Bott trajectories, whose broken strata are
fibre products over critical submanifolds.

## Main definitions

* `Orientation.fiberProduct`: the orientation of the fibre product of two transverse maps.

## Main results

* `Orientation.shortExact_fiberProduct`: the defining identity
  `[X][Y] = (-1) ^ (dim Y · dim T) [Q][T]`.
* `Orientation.fiberProduct_eq_iff`: the fibre product orientation is the unique orientation
  satisfying that identity.
* `Orientation.map_fiberProduct_comm`: the sign of exchanging the factors of a fibre product.
* `Orientation.map_fiberProduct_assoc`: iterated fibre product orientations are associative.
* `Orientation.transverse_fiberProduct_left`, `Orientation.transverse_fiberProduct_right`: the
  boundary formula for fibre product orientations.

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

namespace Orientation

variable [FiniteDimensional K X] [FiniteDimensional K Y] [FiniteDimensional K T]
  {α : X →ₗ[K] T} {β : Y →ₗ[K] T} {x y t q : ℕ}

omit [LinearOrder K] [IsStrictOrderedRing K] [FiniteDimensional K T] in
/-- `LinearMap.finrank_ker_coprod_neg_add` in terms of the dimensions `x`, `y`, `t` and `q`. -/
private theorem finrank_ker_coprod_neg (h : Function.Surjective (α.coprod (-β)))
    (hx : finrank K X = x) (hy : finrank K Y = y) (ht : finrank K T = t) (hq : q + t = x + y) :
    finrank K (LinearMap.ker (α.coprod (-β))) = q := by
  have := LinearMap.finrank_ker_coprod_neg_add h
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

/-- Scaling the orientation of the first factor by a unit scales the fibre product orientation. -/
@[simp]
theorem fiberProduct_units_smul_left (u : Kˣ) :
    fiberProduct h (u • ox) oy ot hx hy ht hq = u • fiberProduct h ox oy ot hx hy ht hq :=
  Module.Ray.units_smul_of_map_neg (F := (fiberProduct h · oy ot hx hy ht hq))
    (fiberProduct_neg_left h · oy ot hx hy ht hq) u ox

/-- Scaling the orientation of the second factor by a unit scales the fibre product orientation. -/
@[simp]
theorem fiberProduct_units_smul_right (u : Kˣ) :
    fiberProduct h ox (u • oy) ot hx hy ht hq = u • fiberProduct h ox oy ot hx hy ht hq :=
  Module.Ray.units_smul_of_map_neg (F := (fiberProduct h ox · ot hx hy ht hq))
    (fiberProduct_neg_right h ox · ot hx hy ht hq) u oy

/-- Scaling the orientation of the base by a unit scales the fibre product orientation. -/
@[simp]
theorem fiberProduct_units_smul_base (u : Kˣ) :
    fiberProduct h ox oy (u • ot) hx hy ht hq = u • fiberProduct h ox oy ot hx hy ht hq :=
  Module.Ray.units_smul_of_map_neg (F := (fiberProduct h ox oy · hx hy ht hq))
    (fiberProduct_neg_base h ox oy · hx hy ht hq) u ot

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
    (LinearEquiv.prodComm K X Y) (LinearEquiv.neg K) (by ext <;> simp [σ])
    (by rw [LinearMap.coprod_neg_comp_prodComm]; ext <;> simp) oq ot
  have hfin : (finCongr (add_comm y x)).trans (finCongr hq.symm) =
      finCongr (hq.trans (add_comm x y)).symm := by
    ext; simp
  have hneg : map (Fin t) (LinearEquiv.neg K) ot = (-1 : Kˣ) ^ t • ot := by
    rw [map_linearEquiv_neg ot (by rw [Fintype.card_fin, ht]), ht]
  -- Solve `hnat` for the subspace-first orientation of `σ oq`, then compare with the defining
  -- identity of `oq'`.
  rw [hneg, shortExact_units_smul_right, eq_comm, smul_eq_iff_eq_inv_smul] at hnat
  rw [← shortExact_inj_left (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map _) h'
    hQ' ht ot, hnat, shortExact_units_smul_left, shortExact_fiberProduct, shortExact_fiberProduct]
  simp only [map_reindex, map_units_smul, map_prodComm_prod, reindex_units_smul, ← reindex_trans,
    hfin, smul_smul, ← inv_pow, inv_neg_one, ← pow_add]
  -- The two exponents differ by the even number `2 * (x * t)`.
  congr 1
  rw [show x * y + t * (x + y) + t + x * t = t + (y * t + x * y) + 2 * (x * t) by ring,
    pow_add _ _ (2 * (x * t)), (even_two_mul _).neg_one_pow, mul_one]

/-! ### Associativity -/

section Assoc

variable {Z S : Type*} [AddCommGroup Z] [Module K Z] [AddCommGroup S] [Module K S]
  [FiniteDimensional K Z] [FiniteDimensional K S] {γ : Y →ₗ[K] S} {δ : Z →ₗ[K] S}
  {z s q₁ q₂ r : ℕ}

open LinearMap in
/-- **Associativity of fibre product orientations.** For `α : X → T`, `β : Y → T`, `γ : Y → S`
and `δ : Z → S`, the reassociation `(X ×_T Y) ×_S Z ≃ X ×_T (Y ×_S Z)`
(`LinearMap.fiberProductAssoc`) carries the fibre product orientation of `X ×_T Y` and `Z` to
that of `X` and `Y ×_S Z`, with no sign: in the formal notation `[X][T]^∨[Y]`, both are
`[X][T]^∨[Y][S]^∨[Z]`. Only transversality of the left bracketing is assumed; that of the right
bracketing follows (`LinearMap.surjective_coprod_of_comp_left`,
`LinearMap.surjective_coprod_neg_assoc_outer`). -/
theorem map_fiberProduct_assoc (h₁ : Function.Surjective (α.coprod (-β)))
    (h₁₂ : Function.Surjective
      ((γ ∘ₗ snd K X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ)))
    (ox : Orientation K X (Fin x)) (oy : Orientation K Y (Fin y)) (oz : Orientation K Z (Fin z))
    (ot : Orientation K T (Fin t)) (os : Orientation K S (Fin s)) (hx : finrank K X = x)
    (hy : finrank K Y = y) (hz : finrank K Z = z) (ht : finrank K T = t) (hs : finrank K S = s)
    (hq₁ : q₁ + t = x + y) (hr₁ : r + s = q₁ + z) (hq₂ : q₂ + s = y + z)
    (hr₂ : r + t = x + q₂) :
    map (Fin r) (fiberProductAssoc α β γ δ)
        (fiberProduct h₁₂ (fiberProduct h₁ ox oy ot hx hy ht hq₁) oz os
          (by have := finrank_ker_coprod_neg_add h₁; omega) hz hs hr₁) =
      fiberProduct (β := β ∘ₗ fst K Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)
        (surjective_coprod_neg_assoc_outer h₁ h₁₂) ox
        (fiberProduct (surjective_coprod_of_comp_left h₁₂) oy oz os hy hz hs hq₂) ot hx
        (by have := finrank_ker_coprod_neg_add (surjective_coprod_of_comp_left h₁₂); omega) ht
        hr₂ := by
  have h₂ := surjective_coprod_of_comp_left h₁₂
  have h₂₂ := surjective_coprod_neg_assoc_outer h₁ h₁₂
  have hQ₁ := finrank_ker_coprod_neg h₁ hx hy ht hq₁
  have hQ₂ := finrank_ker_coprod_neg h₂ hy hz hs hq₂
  have hR₁ := finrank_ker_coprod_neg h₁₂ hQ₁ hz hs hr₁
  have hR₂ := finrank_ker_coprod_neg h₂₂ hx hQ₂ ht hr₂
  set oQ₁ := fiberProduct h₁ ox oy ot hx hy ht hq₁
  set oQ₂ := fiberProduct h₂ oy oz os hy hz hs hq₂
  set oR₁ := fiberProduct h₁₂ oQ₁ oz os hQ₁ hz hs hr₁
  set oR₂ := fiberProduct h₂₂ ox oQ₂ ot hx hQ₂ ht hr₂
  -- `(X ×_T Y) ×_S Z` is cut out of `(X × Y) × Z` first by `(ξ, η) ↦ α ξ - β η` and then by
  -- `η ↦ γ η - δ ζ`; `X ×_T (Y ×_S Z)` is cut out of `X × (Y × Z)` in the opposite order.
  have e₁ : (γ ∘ₗ snd K X Y).coprod (-δ) ∘ₗ
      (ker (α.coprod (-β))).subtype.prodMap (LinearMap.id : Z →ₗ[K] Z) =
        (γ ∘ₗ snd K X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ) := by
    ext <;> simp
  have e₂ : α.coprod (-(β ∘ₗ fst K Y Z)) ∘ₗ
      (LinearMap.id : X →ₗ[K] X).prodMap (ker (γ.coprod (-δ))).subtype =
        α.coprod (-(β ∘ₗ fst K Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)) := by
    ext <;> simp
  have hU₂ : finrank K (X × ker (γ.coprod (-δ))) = r + t := by
    rw [finrank_prod, hQ₂, hx]
    omega
  have E := map_shortExact_shortExact (Submodule.injective_subtype _) (exact_subtype_ker_map _)
    h₁₂ (injective_prodMap (Submodule.injective_subtype _) Function.injective_id)
    (exact_subtype_ker_map _).prodMap_id_comp_fst (surjective_comp h₁ fst_surjective) e₁
    (Submodule.injective_subtype _) (exact_subtype_ker_map _) h₂₂
    (injective_prodMap Function.injective_id (Submodule.injective_subtype _))
    (exact_subtype_ker_map _).id_prodMap_comp_snd (surjective_comp h₂ snd_surjective) e₂
    (fiberProductAssoc α β γ δ) (LinearEquiv.prodAssoc K X Y Z)
    prodMap_subtype_fiberProductAssoc_apply (fun _ ↦ by simp) (fun _ ↦ by simp) oR₁ ot os hR₁
    ht hs (by rw [finrank_prod, hQ₁, hz]; omega) hU₂
  -- By `E`, it suffices to compare the orientations of `X × (Y × Z)` induced through the second
  -- tower; both are products of `ox`, `oy` and `oz` up to explicit signs.
  rw [← shortExact_inj_left (Submodule.injective_subtype _) (exact_subtype_ker_map _) h₂₂ hR₂ ht
      ot, ← shortExact_inj_left
      (injective_prodMap Function.injective_id (Submodule.injective_subtype _))
      (exact_subtype_ker_map _).id_prodMap_comp_snd (surjective_comp h₂ snd_surjective) hU₂ hs os]
  apply (MulAction.injective ((-1 : Kˣ) ^ (t * s))).comp
    (reindex K (X × Y × Z) (finCongr (add_right_comm r t s))).injective
  simp only [Function.comp_apply]
  -- The first tower is `([X][Y])[Z]` up to sign: unfold `oR₁` and then `oQ₁`.
  rw [shortExact_fiberProduct,
    shortExact_reindex_finCongr_left,
    shortExact_units_smul_left, shortExact_prodMap_id (Submodule.injective_subtype _)
      (exact_subtype_ker_map _) h₁ oQ₁ oz ot hQ₁ hz ht, shortExact_fiberProduct,
    prod_reindex_finCongr_left, prod_units_smul_left] at E
  -- The second tower is `[X]([Y][Z])` up to sign: unfold `oR₂` and then `oQ₂`.
  rw [shortExact_fiberProduct,
    shortExact_reindex_finCongr_left,
    shortExact_units_smul_left, shortExact_id_prodMap (Submodule.injective_subtype _)
      (exact_subtype_ker_map _) h₂ ox oQ₂ os hx hQ₂ hs, shortExact_fiberProduct,
    prod_reindex_finCongr_right, prod_units_smul_right, ← E]
  -- Normalize the reindexings and collect the signs.
  simp only [map_reindex, map_units_smul, reindex_units_smul, smul_smul, ← pow_add,
    reindex_finCongr_reindex_finCongr, map_prodAssoc_prod]
  -- The two signs agree since `(q₂ + s) t = (y + z) t`.
  have hexp : t * s + (q₂ * t + z * s) = z * s + (z * t + y * t) := by
    have h := congrArg (· * t) hq₂
    simp only [add_mul] at h
    linarith [mul_comm s t]
  rw [hexp]

end Assoc

end Orientation

/-! ### Boundaries -/

namespace Orientation

variable {K X Y T : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y] [AddCommGroup T] [Module K T]
  [FiniteDimensional K X] [FiniteDimensional K Y] [FiniteDimensional K T]
  {α : X →ₗ[K] T} {β : Y →ₗ[K] T} {x y t q : ℕ}

open LinearMap in
/-- **The boundary of a fibre product along the first factor.** Let `p` be a hyperplane in `X`,
with `α ∘ p.subtype` transverse to `β`, and let `v` be a vector of the fibre product
`Q = X ×_T Y` with `v.1 ∉ p`, so that `p ×_T Y` is a hyperplane in `Q` not containing `v`. The
orientation of `p ×_T Y` induced by the fibre product orientation of `Q` and `v` is the fibre
product orientation for the orientation of `p` induced by `[X]` and `v.1`. This is the first term
of the boundary formula `∂(X ×_T Y) = (∂X) ×_T Y + (-1) ^ (dim X + dim T) X ×_T ∂Y` for the
outward-first boundary orientation. -/
theorem transverse_fiberProduct_left {p : Submodule K X}
    (h : Function.Surjective ((α ∘ₗ p.subtype).coprod (-β))) {v : ker (α.coprod (-β))}
    (hv₁ : (v : X × Y).1 ∉ p) (ox : Orientation K X (Fin (x + 1))) (oy : Orientation K Y (Fin y))
    (ot : Orientation K T (Fin t)) (hX : finrank K X = x + 1) (hp : finrank K p = x)
    (hy : finrank K Y = y) (ht : finrank K T = t) (hq : q + t = x + y)
    (hQ : finrank K (ker (α.coprod (-β))) = q + 1)
    (hW : finrank K (range (fiberProductInclusionLeft α β p)) = q) :
    (fiberProduct (surjective_coprod_of_comp_left h) ox oy ot hX hy ht
        (by omega)).transverse hQ hW (mt mem_range_fiberProductInclusionLeft.1 hv₁) =
      map (Fin q) (LinearEquiv.ofInjective _ (fiberProductInclusionLeft_injective p))
        (fiberProduct h (ox.transverse hX hp hv₁) oy ot hp hy ht hq) := by
  have hv : v ∉ range (fiberProductInclusionLeft α β p) :=
    mt mem_range_fiberProductInclusionLeft.1 hv₁
  set ι := fiberProductInclusionLeft α β p
  set eι := LinearEquiv.ofInjective ι (fiberProductInclusionLeft_injective p)
  set J := p.subtype.prodMap (LinearMap.id : Y →ₗ[K] Y)
  have hJ : Function.Injective J := p.injective_subtype.prodMap Function.injective_id
  have h' := surjective_coprod_of_comp_left h
  set fp := fiberProduct h' ox oy ot hX hy ht (by omega : q + 1 + t = x + 1 + y)
  -- Write the boundary orientation as the image of an orientation `o` of `p ×_T Y`.
  set o := (map (Fin q) eι).symm (fp.transverse hQ hW hv)
  have ho : fp.transverse hQ hW hv = map (Fin q) eι o := (Equiv.apply_symm_apply _ _).symm
  rw [ho]
  congr 1
  have hQ' : finrank K (ker ((α ∘ₗ p.subtype).coprod (-β))) = q := by
    have := finrank_ker_coprod_neg_add h
    omega
  refine ((fiberProduct_eq_iff h _ oy ot hp hy ht hq hQ' o).2 ?_).symm
  have hV : finrank K (X × Y) = q + t + 1 := by rw [Module.finrank_prod]; omega
  have hVJ : finrank K (range J) = q + t := by
    rw [finrank_range_of_inj hJ, Module.finrank_prod, hp, hy]; omega
  have hfu : (ker (α.coprod (-β))).subtype v ∉ range J := by simpa [J] using hv₁
  -- Restrict the defining sequence `0 → Q → X × Y → T → 0` to `0 → p ×_T Y → p × Y → T → 0`,
  -- then compute the boundary orientation of `[X][Y]` along `p × Y`.
  have hG := transverse_shortExact (Submodule.injective_subtype _)
    (exact_subtype_ker_map _) h' (Submodule.injective_subtype _) (exact_subtype_ker_map _) h
    (fiberProductInclusionLeft_injective p) hJ (by ext <;> simp [J]) (by ext <;> simp [J]) hv hfu
    fp o ot hQ hQ' ht hW hV hVJ ho
  rw [shortExact_fiberProduct, ← reindex_trans, reindex_units_smul, transverse_units_smul,
    show (finCongr (by omega : x + 1 + y = q + 1 + t)).trans (finCongr (Nat.add_right_comm q 1 t)) =
      finCongr (by omega) from Equiv.ext fun _ ↦ Fin.ext rfl,
    transverse_prod_left (v := (ker (α.coprod (-β))).subtype v) hv₁ ox oy hX hp hy hq.symm hV
      hVJ hfu, ← map_units_smul,
    ← reindex_units_smul] at hG
  exact ((map (Fin (q + t)) (LinearEquiv.ofInjective J hJ)).injective hG).symm

open LinearMap in
/-- **The boundary of a fibre product along the second factor.** Let `p` be a hyperplane in `Y`,
with `α` transverse to `β ∘ p.subtype`, and let `v` be a vector of the fibre product
`Q = X ×_T Y` with `v.2 ∉ p`, so that `X ×_T p` is a hyperplane in `Q` not containing `v`. The
orientation of `X ×_T p` induced by the fibre product orientation of `Q` and `v` is
`(-1) ^ (dim X + dim T)` times the fibre product orientation for the orientation of `p` induced by
`[Y]` and `v.2`. This is the second term of the boundary formula
`∂(X ×_T Y) = (∂X) ×_T Y + (-1) ^ (dim X + dim T) X ×_T ∂Y` for the outward-first boundary
orientation. -/
theorem transverse_fiberProduct_right {p : Submodule K Y}
    (h : Function.Surjective (α.coprod (-(β ∘ₗ p.subtype)))) {v : ker (α.coprod (-β))}
    (hv₂ : (v : X × Y).2 ∉ p) (ox : Orientation K X (Fin x)) (oy : Orientation K Y (Fin (y + 1)))
    (ot : Orientation K T (Fin t)) (hx : finrank K X = x) (hY : finrank K Y = y + 1)
    (hp : finrank K p = y) (ht : finrank K T = t) (hq : q + t = x + y)
    (hQ : finrank K (ker (α.coprod (-β))) = q + 1)
    (hW : finrank K (range (fiberProductInclusionRight α β p)) = q) :
    (fiberProduct (surjective_coprod_neg_of_comp_right h) ox oy ot hx hY ht
        (by omega)).transverse hQ hW (mt mem_range_fiberProductInclusionRight.1 hv₂) =
      (-1 : Kˣ) ^ (x + t) • map (Fin q) (LinearEquiv.ofInjective _
        (fiberProductInclusionRight_injective p))
          (fiberProduct h ox (oy.transverse hY hp hv₂) ot hx hp ht hq) := by
  have hv : v ∉ range (fiberProductInclusionRight α β p) :=
    mt mem_range_fiberProductInclusionRight.1 hv₂
  set ι := fiberProductInclusionRight α β p
  set eι := LinearEquiv.ofInjective ι (fiberProductInclusionRight_injective p)
  set J := (LinearMap.id : X →ₗ[K] X).prodMap p.subtype
  have hJ : Function.Injective J := Function.injective_id.prodMap p.injective_subtype
  have h' := surjective_coprod_neg_of_comp_right h
  set fp := fiberProduct h' ox oy ot hx hY ht (by omega : q + 1 + t = x + (y + 1))
  -- Write the boundary orientation as the image of an orientation `o` of `X ×_T p`.
  set o := (map (Fin q) eι).symm (fp.transverse hQ hW hv)
  have ho : fp.transverse hQ hW hv = map (Fin q) eι o := (Equiv.apply_symm_apply _ _).symm
  rw [ho, ← map_units_smul, ← fiberProduct_units_smul_base]
  congr 1
  have hQ' : finrank K (ker (α.coprod (-(β ∘ₗ p.subtype)))) = q := by
    have := finrank_ker_coprod_neg_add h
    omega
  refine ((fiberProduct_eq_iff h ox _ _ hx hp ht hq hQ' o).2 ?_).symm
  have hV : finrank K (X × Y) = q + t + 1 := by rw [Module.finrank_prod]; omega
  have hVJ : finrank K (range J) = q + t := by
    rw [finrank_range_of_inj hJ, Module.finrank_prod, hx, hp]; omega
  have hfu : (ker (α.coprod (-β))).subtype v ∉ range J := by simpa [J] using hv₂
  -- Restrict the defining sequence `0 → Q → X × Y → T → 0` to `0 → X ×_T p → X × p → T → 0`,
  -- then compute the boundary orientation of `[X][Y]` along `X × p`.
  have hG := transverse_shortExact (Submodule.injective_subtype _)
    (exact_subtype_ker_map _) h' (Submodule.injective_subtype _) (exact_subtype_ker_map _) h
    (fiberProductInclusionRight_injective p) hJ (by ext <;> simp [J]) (by ext <;> simp [J]) hv hfu
    fp o ot hQ hQ' ht hW hV hVJ ho
  rw [shortExact_fiberProduct, ← reindex_trans, reindex_units_smul, transverse_units_smul,
    show (finCongr (by omega : x + (y + 1) = q + 1 + t)).trans
        (finCongr (Nat.add_right_comm q 1 t)) = finCongr (by omega) from
      Equiv.ext fun _ ↦ Fin.ext rfl,
    transverse_prod_right (v := (ker (α.coprod (-β))).subtype v) hv₂ ox oy hx hY hp hq.symm hV
      hVJ hfu, smul_smul, ← map_units_smul, ← reindex_units_smul] at hG
  rw [shortExact_units_smul_right,
    ← (map (Fin (q + t)) (LinearEquiv.ofInjective J hJ)).injective hG,
    reindex_units_smul, reindex_units_smul, smul_smul]
  -- The signs `(-1) ^ (x + t)`, `(-1) ^ ((y + 1) * t)` and `(-1) ^ x` combine to `(-1) ^ (y * t)`.
  congr 1
  rw [← pow_add, ← pow_add, show x + t + ((y + 1) * t + x) = y * t + 2 * (x + t) by ring,
    pow_add, (even_two_mul _).neg_one_pow, mul_one]

end Orientation
