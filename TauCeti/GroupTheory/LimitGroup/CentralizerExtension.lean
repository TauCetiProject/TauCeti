/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic
public import TauCeti.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.HNNExtension
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.PushoutI

/-!
# Extensions of centralizers

For a group `G`, an element `u : G` and `n : ℕ`, the *extension of the centralizer* of `u` by
`ℤⁿ` is the amalgamated product
`G(u, ℤⁿ) = G ∗_{C_G(u)} (C_G(u) × ℤⁿ)`
of `G` and `C_G(u) × ℤⁿ` over the full centralizer `C_G(u)`, with `C_G(u)` embedded in the second
factor as `c ↦ (c, 1)`. It contains `G` and `n` new letters `t₀, …, tₙ₋₁`, the standard generators
of `ℤⁿ`, which commute with each other and with every element of `C_G(u)`; a homomorphism out of
`G(u, ℤⁿ)` is determined by any such data (`CentralizerExt.homEquiv`). For `n = 1` this is the HNN
extension `⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩`.

Iterated extensions of centralizers are the basic examples of fully residually free groups: over a
nonabelian CSA group `G` with the big powers property and `u` not a proper power, the retractions
`t ↦ u ^ k` of `G(u, ℤ)` onto `G` discriminate it by `G` (see Kharlampovich–Myasnikov,
*Implicit function theorem over free groups*, §2.5). This file sets up the construction for
arbitrary `u` and `n`, its universal property and these retractions, and compares it with `G` for
`n = 0`, with `G × ℤⁿ` for central `u`, and with Mathlib's HNN extension for `n = 1`. The
construction always uses the full centralizer and imposes no condition on `u` or `n`;
`IsAdmissibleCentralizerStep u n` records the conditions imposed on a step of an iterated extension
of centralizers.

The amalgam is Mathlib's `Monoid.PushoutI` over the `Bool`-indexed family `CentralizerExtFactor`,
so its normal form theory (`Monoid.PushoutI.NormalWord`) applies directly.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt u n`: the extension `G(u, ℤⁿ)`.
* `TauCeti.LimitGroup.CentralizerExt.of`: the inclusion of `G`.
* `TauCeti.LimitGroup.CentralizerExt.t`: the new letters `tᵢ`.
* `TauCeti.LimitGroup.CentralizerExt.lift`, `TauCeti.LimitGroup.CentralizerExt.homEquiv`: the
  universal property.
* `TauCeti.LimitGroup.CentralizerExt.retraction k`: the retraction `tᵢ ↦ u ^ kᵢ` onto `G`.
* `TauCeti.LimitGroup.IsAdmissibleCentralizerStep u n`: `u` is not a proper power and `0 < n`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.of_injective`: `G` embeds in `G(u, ℤⁿ)`.
* `TauCeti.LimitGroup.CentralizerExt.zeroEquiv`: `G(u, ℤ⁰) ≃* G`.
* `TauCeti.LimitGroup.CentralizerExt.equivProdOfMemCenter`: for central `u`,
  `G(u, ℤⁿ) ≃* G × ℤⁿ`.
* `TauCeti.LimitGroup.CentralizerExt.equivHNNExtension`: `G(u, ℤ)` is the HNN extension of `G`
  along the identity of `C_G(u)`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*,
  J. Algebra 200 (1998), §1, Definition 5.
-/

public section

open Subgroup

universe u v

namespace TauCeti.LimitGroup

variable {G : Type u} [Group G]

/-- The two factors of the extension `G(u, ℤⁿ)` as a `Bool`-indexed family: `G` at `false` and
`C_G(u) × ℤⁿ` at `true`, with `ℤⁿ` written as `Fin n → Multiplicative ℤ`. -/
abbrev CentralizerExtFactor (u : G) (n : ℕ) (b : Bool) : Type u :=
  cond b (centralizer {u} × (Fin n → Multiplicative ℤ)) G

instance (u : G) (n : ℕ) (b : Bool) : Group (CentralizerExtFactor u n b) :=
  Bool.rec (motive := fun b => Group (CentralizerExtFactor u n b))
    (inferInstanceAs (Group G))
    (inferInstanceAs (Group (centralizer {u} × (Fin n → Multiplicative ℤ)))) b

/-- The two embeddings of `C_G(u)` amalgamated in `G(u, ℤⁿ)`: the inclusion into `G` and
`c ↦ (c, 1)` into `C_G(u) × ℤⁿ`. -/
def centralizerExtMap (u : G) (n : ℕ) :
    ∀ b, centralizer {u} →* CentralizerExtFactor u n b
  | false => (centralizer {u}).subtype
  | true => MonoidHom.inl _ _

@[simp] theorem centralizerExtMap_false (u : G) (n : ℕ) :
    centralizerExtMap u n false = (centralizer {u}).subtype := (rfl)

@[simp] theorem centralizerExtMap_true (u : G) (n : ℕ) :
    centralizerExtMap u n true = MonoidHom.inl (centralizer {u}) (Fin n → Multiplicative ℤ) :=
  (rfl)

theorem centralizerExtMap_injective (u : G) (n : ℕ) (b : Bool) :
    Function.Injective (centralizerExtMap u n b) := by
  cases b
  · exact Subtype.val_injective
  · exact fun _ _ h => congrArg Prod.fst h

/-- The *extension of the centralizer* of `u` by `ℤⁿ`, the amalgamated product
`G(u, ℤⁿ) = G ∗_{C_G(u)} (C_G(u) × ℤⁿ)` over the full centralizer `C_G(u)`. -/
abbrev CentralizerExt (u : G) (n : ℕ) : Type u :=
  Monoid.PushoutI (centralizerExtMap u n)

namespace CentralizerExt

variable {u : G} {n : ℕ} {K : Type v}

open Monoid.PushoutI

/-- The inclusion of `G` in `G(u, ℤⁿ)`. -/
def of : G →* CentralizerExt u n :=
  Monoid.PushoutI.of (φ := centralizerExtMap u n) false

/-- The new letter `tᵢ` of `G(u, ℤⁿ)`, the `i`-th standard generator of `ℤⁿ`. -/
def t (i : Fin n) : CentralizerExt u n :=
  Monoid.PushoutI.of (φ := centralizerExtMap u n) true (1, Pi.mulSingle i (.ofAdd 1))

/-- `G` embeds in `G(u, ℤⁿ)`. -/
theorem of_injective : Function.Injective (of : G →* CentralizerExt u n) :=
  Monoid.PushoutI.of_injective (centralizerExtMap_injective u n) false

@[simp] theorem of_inj {g h : G} : (of g : CentralizerExt u n) = of h ↔ g = h :=
  of_injective.eq_iff

/-- An element of `C_G(u)` is also the image of `(c, 1)` from the second factor. -/
private theorem of_true_inl (c : centralizer {u}) :
    Monoid.PushoutI.of (φ := centralizerExtMap u n) true (c, 1) = of (c : G) := by
  have h₁ := of_apply_eq_base (centralizerExtMap u n) true c
  have h₂ := of_apply_eq_base (centralizerExtMap u n) false c
  simp only [centralizerExtMap_true, centralizerExtMap_false, Subgroup.coe_subtype] at h₁ h₂
  -- `MonoidHom.inl _ _ c` is `(c, 1)` by definition, and `of` is the inclusion at `false`; `simp`
  -- cannot see the former through the instance on the `Bool`-indexed factor.
  exact h₁.trans h₂.symm

/-- The new letters commute with every element of `C_G(u)`. -/
theorem commute_of_t {c : G} (hc : c ∈ centralizer {u}) (i : Fin n) :
    Commute (of c : CentralizerExt u n) (t i) := by
  rw [← of_true_inl ⟨c, hc⟩, t]
  exact ((Commute.one_right _).prod (Commute.one_left _)).map _

/-- The new letters commute with each other. -/
theorem commute_t_t (i j : Fin n) : Commute (t i : CentralizerExt u n) (t j) :=
  ((Commute.one_right 1).prod (Commute.all _ _)).map _

/-- Homomorphisms out of `G(u, ℤⁿ)` agree when they agree on `G` and on the new letters. -/
@[ext high]
theorem hom_ext [Monoid K] {f g : CentralizerExt u n →* K} (hof : f.comp of = g.comp of)
    (ht : ∀ i, f (t i) = g (t i)) : f = g := by
  refine Monoid.PushoutI.hom_ext_nonempty fun b => ?_
  cases b
  · exact hof
  · -- On `C_G(u) × ℤⁿ`, agree separately on `C_G(u) × 1` and on `1 × ℤⁿ`.
    have hl : ∀ c : centralizer {u}, f (Monoid.PushoutI.of (φ := centralizerExtMap u n) true
        (c, 1)) = g (Monoid.PushoutI.of (φ := centralizerExtMap u n) true (c, 1)) := fun c => by
      simpa [of_true_inl] using DFunLike.congr_fun hof (c : G)
    have hr : (f.comp (Monoid.PushoutI.of (φ := centralizerExtMap u n) true)).comp
        (MonoidHom.inr _ _) =
        (g.comp (Monoid.PushoutI.of (φ := centralizerExtMap u n) true)).comp
          (MonoidHom.inr _ _) :=
      MonoidHom.pi_ext_mint fun i => ht i
    refine MonoidHom.ext fun ⟨c, v⟩ => ?_
    have hcv : ((c, v) : centralizer {u} × (Fin n → Multiplicative ℤ)) = (c, 1) * (1, v) := by
      simp
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [hcv, map_mul, map_mul, map_mul, hl]
    exact congrArg _ (DFunLike.congr_fun hr v)

variable [Group K]

/-- A homomorphism out of `G(u, ℤⁿ)` is given by a homomorphism `φ` on `G` and pairwise commuting
images `τ i` of the new letters that commute with `φ (C_G(u))`. -/
def lift (φ : G →* K) (τ : Fin n → K) (hτ : ∀ i j, Commute (τ i) (τ j))
    (hφ : ∀ c ∈ centralizer {u}, ∀ i, Commute (φ c) (τ i)) : CentralizerExt u n →* K :=
  Monoid.PushoutI.lift
    (fun b => Bool.rec (motive := fun b => CentralizerExtFactor u n b →* K) φ
      ((φ.comp (centralizer {u}).subtype).noncommCoprod (zpowersPiHom τ hτ)
        fun c v => commute_zpowersPiHom (x := (φ.comp (centralizer {u}).subtype) c) (hφ c c.2) v)
      b)
    (φ.comp (centralizer {u}).subtype)
    fun b => by
      cases b
      · rfl
      · exact MonoidHom.noncommCoprod_comp_inl _ _ _

section lift

variable (φ : G →* K) (τ : Fin n → K) (hτ : ∀ i j, Commute (τ i) (τ j))
  (hφ : ∀ c ∈ centralizer {u}, ∀ i, Commute (φ c) (τ i))

@[simp] theorem lift_of (g : G) : lift φ τ hτ hφ (of g) = φ g := by
  rw [lift, of, Monoid.PushoutI.lift_of]

@[simp] theorem lift_comp_of : (lift φ τ hτ hφ).comp of = φ :=
  MonoidHom.ext (lift_of φ τ hτ hφ)

@[simp] theorem lift_t (i : Fin n) : lift φ τ hτ hφ (t i) = τ i := by
  rw [t, lift, Monoid.PushoutI.lift_of]
  -- The factor homomorphism is stated through the `Bool`-indexed family; restate it on the product.
  exact (MonoidHom.noncommCoprod_apply _ _ _ _).trans (by simp [zpowersPiHom_mulSingle])

end lift

/-- The universal property of `G(u, ℤⁿ)`: homomorphisms to `K` correspond to homomorphisms
`φ : G →* K` together with pairwise commuting images of the new letters that commute with
`φ (C_G(u))`. -/
def homEquiv : (CentralizerExt u n →* K) ≃
    { p : (G →* K) × (Fin n → K) // (∀ i j, Commute (p.2 i) (p.2 j)) ∧
      ∀ c ∈ centralizer {u}, ∀ i, Commute (p.1 c) (p.2 i) } where
  toFun f := ⟨(f.comp of, fun i => f (t i)), fun i j => (commute_t_t i j).map f,
    fun _ hc i => (commute_of_t hc i).map f⟩
  invFun p := lift p.1.1 p.1.2 p.2.1 p.2.2
  left_inv f := hom_ext (by simp) (by simp)
  right_inv p := by ext <;> simp

@[simp] theorem homEquiv_apply_coe (f : CentralizerExt u n →* K) :
    (homEquiv f : (G →* K) × (Fin n → K)) = (f.comp of, fun i => f (t i)) := (rfl)

@[simp] theorem homEquiv_symm_apply (p) :
    (homEquiv (u := u) (n := n) (K := K)).symm p = lift p.1.1 p.1.2 p.2.1 p.2.2 := (rfl)

/-- For `k : Fin n → ℤ`, the retraction of `G(u, ℤⁿ)` onto `G` sending `tᵢ` to `u ^ kᵢ`. -/
def retraction (k : Fin n → ℤ) : CentralizerExt u n →* G :=
  lift (.id G) (fun i => u ^ k i) (fun _ _ => Commute.zpow_zpow_self _ _ _)
    fun _ hc _ => Commute.zpow_right (mem_centralizer_singleton_iff.mp hc) _

@[simp] theorem retraction_of (k : Fin n → ℤ) (g : G) :
    retraction k (of g : CentralizerExt u n) = g :=
  lift_of _ _ _ _ g

@[simp] theorem retraction_t (k : Fin n → ℤ) (i : Fin n) :
    retraction k (t i : CentralizerExt u n) = u ^ k i :=
  lift_t _ _ _ _ i

@[simp] theorem retraction_comp_of (k : Fin n → ℤ) :
    (retraction k).comp (of : G →* CentralizerExt u n) = .id G :=
  lift_comp_of _ _ _ _

/-- Extending a centralizer by `ℤ⁰` does not change the group: `G(u, ℤ⁰) ≃* G`. -/
def zeroEquiv : CentralizerExt u 0 ≃* G :=
  (retraction 0).toMulEquiv of (hom_ext (by ext; simp) finZeroElim) (retraction_comp_of 0)

@[simp] theorem zeroEquiv_of (g : G) : zeroEquiv (of g : CentralizerExt u 0) = g :=
  retraction_of (u := u) (n := 0) 0 g

@[simp] theorem zeroEquiv_symm_apply (g : G) : (zeroEquiv (u := u)).symm g = of g := (rfl)

/-- The second factor `ℤⁿ` of the amalgam, mapped into `G(u, ℤⁿ)`. -/
private def ofPi : (Fin n → Multiplicative ℤ) →* CentralizerExt u n :=
  (Monoid.PushoutI.of (φ := centralizerExtMap u n) true).comp (MonoidHom.inr _ _)

private theorem ofPi_mulSingle (i : Fin n) :
    (ofPi (Pi.mulSingle i (.ofAdd 1)) : CentralizerExt u n) = t i := (rfl)

private theorem commute_of_ofPi (hu : u ∈ center G) (g : G) (v : Fin n → Multiplicative ℤ) :
    Commute (of g) (ofPi v : CentralizerExt u n) := by
  rw [← of_true_inl ⟨g, mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hu g)⟩]
  exact (MonoidHom.commute_inl_inr _ _).map _

/-- The homomorphism `G(u, ℤⁿ) →* G × ℤⁿ` sending `g` to `(g, 1)` and `tᵢ` to the `i`-th
standard generator. -/
private def toProd : CentralizerExt u n →* G × (Fin n → Multiplicative ℤ) :=
  lift (.inl _ _) (fun i => (1, Pi.mulSingle i (.ofAdd 1)))
    (fun _ _ => (Commute.one_right 1).prod (.all _ _)) fun _ _ _ => MonoidHom.commute_inl_inr _ _

private theorem toProd_of (g : G) : toProd (of g : CentralizerExt u n) = (g, 1) :=
  lift_of _ _ _ _ g

private theorem toProd_t (i : Fin n) :
    toProd (t i : CentralizerExt u n) = (1, Pi.mulSingle i (.ofAdd 1)) :=
  lift_t _ _ _ _ i

/-- If `u` is central, its centralizer is all of `G`, and extending it by `ℤⁿ` is the direct
product: `G(u, ℤⁿ) ≃* G × ℤⁿ`. -/
def equivProdOfMemCenter (hu : u ∈ center G) :
    CentralizerExt u n ≃* G × (Fin n → Multiplicative ℤ) :=
  toProd.toMulEquiv (of.noncommCoprod ofPi (commute_of_ofPi hu))
    (hom_ext (by ext; simp [toProd_of]) fun i => by simp [toProd_t, ofPi_mulSingle])
    (by
      have hv : (toProd (u := u) (n := n)).comp ofPi = .inr _ _ :=
        MonoidHom.pi_ext_mint fun i => by simp [ofPi_mulSingle, toProd_t]
      refine MonoidHom.ext fun ⟨x, v⟩ => ?_
      simp [toProd_of, ← MonoidHom.comp_apply _ ofPi, hv])

@[simp] theorem equivProdOfMemCenter_of (hu : u ∈ center G) (g : G) :
    equivProdOfMemCenter (n := n) hu (of g) = (g, 1) :=
  toProd_of g

@[simp] theorem equivProdOfMemCenter_t (hu : u ∈ center G) (i : Fin n) :
    equivProdOfMemCenter hu (t i) = (1, Pi.mulSingle i (.ofAdd 1)) :=
  toProd_t i

private theorem commute_hnnExtension_of_t {c : G} (hc : c ∈ centralizer {u}) :
    Commute (HNNExtension.of (A := centralizer {u}) (B := centralizer {u}) (φ := .refl _) c)
      HNNExtension.t := by
  have h := HNNExtension.of_mul_t (φ := MulEquiv.refl (centralizer {u})) ⟨c, hc⟩
  simp only [MulEquiv.refl_symm, MulEquiv.refl_apply] at h
  exact h

/-- The homomorphism `G(u, ℤ) →* ⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩` that is the identity on `G` and
sends `t₀` to `t`. -/
private def toHNNExtension :
    CentralizerExt u 1 →* HNNExtension G (centralizer {u}) (centralizer {u}) (.refl _) :=
  lift HNNExtension.of (fun _ => HNNExtension.t) (fun _ _ => Commute.refl _)
    fun _ hc _ => commute_hnnExtension_of_t hc

private theorem toHNNExtension_of (g : G) :
    toHNNExtension (of g : CentralizerExt u 1) = HNNExtension.of g :=
  lift_of _ _ _ _ g

private theorem toHNNExtension_t (i : Fin 1) :
    toHNNExtension (t i : CentralizerExt u 1) = HNNExtension.t :=
  lift_t _ _ _ _ i

/-- The inverse of `toHNNExtension`. -/
private def ofHNNExtension :
    HNNExtension G (centralizer {u}) (centralizer {u}) (.refl _) →* CentralizerExt u 1 :=
  HNNExtension.lift of (t 0) fun c => (commute_of_t c.2 0).symm.eq

private theorem ofHNNExtension_of (g : G) :
    ofHNNExtension (HNNExtension.of g : HNNExtension G (centralizer {u}) (centralizer {u}) _) =
      of g :=
  HNNExtension.lift_of _ _ _ g

private theorem ofHNNExtension_t :
    ofHNNExtension (HNNExtension.t : HNNExtension G (centralizer {u}) (centralizer {u}) _) =
      (t 0 : CentralizerExt u 1) :=
  HNNExtension.lift_t _ _ _

/-- Extending a centralizer by `ℤ` is the HNN extension `⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩` along the
identity of `C_G(u)`. -/
def equivHNNExtension :
    CentralizerExt u 1 ≃* HNNExtension G (centralizer {u}) (centralizer {u}) (.refl _) :=
  toHNNExtension.toMulEquiv ofHNNExtension
    (hom_ext (by ext; simp [toHNNExtension_of, ofHNNExtension_of]) fun i => by
      simp [toHNNExtension_t, ofHNNExtension_t, Subsingleton.elim i 0])
    (HNNExtension.hom_ext (by ext; simp [toHNNExtension_of, ofHNNExtension_of])
      (by simp [toHNNExtension_t, ofHNNExtension_t]))

@[simp] theorem equivHNNExtension_of (g : G) :
    equivHNNExtension (of g : CentralizerExt u 1) = HNNExtension.of g :=
  toHNNExtension_of g

@[simp] theorem equivHNNExtension_t (i : Fin 1) :
    equivHNNExtension (t i : CentralizerExt u 1) = HNNExtension.t :=
  toHNNExtension_t i

end CentralizerExt

/-- A step `G ↦ G(u, ℤⁿ)` of an iterated extension of centralizers is *admissible* when `u` is not
a proper power (in particular `u ≠ 1`) and the added rank `n` is positive. -/
def IsAdmissibleCentralizerStep (u : G) (n : ℕ) : Prop :=
  ¬Group.IsProperPower u ∧ 0 < n

theorem isAdmissibleCentralizerStep_iff {u : G} {n : ℕ} :
    IsAdmissibleCentralizerStep u n ↔ ¬Group.IsProperPower u ∧ 0 < n :=
  Iff.rfl

theorem IsAdmissibleCentralizerStep.ne_one {u : G} {n : ℕ} (h : IsAdmissibleCentralizerStep u n) :
    u ≠ 1 :=
  Group.ne_one_of_not_isProperPower h.1

/-- Extending the centralizer of a basis element of a free group is admissible in every positive
rank. -/
theorem isAdmissibleCentralizerStep_freeGroup_of {α : Type*} (a : α) {n : ℕ} (hn : 0 < n) :
    IsAdmissibleCentralizerStep (FreeGroup.of a) n :=
  ⟨FreeGroup.not_isProperPower_of a, hn⟩

/-- Extending the centralizer of the square of a basis element of a free group is never
admissible. -/
theorem not_isAdmissibleCentralizerStep_freeGroup_of_sq {α : Type*} (a : α) (n : ℕ) :
    ¬IsAdmissibleCentralizerStep (FreeGroup.of a ^ 2) n :=
  fun h => h.1 (FreeGroup.isProperPower_of_sq a)

end TauCeti.LimitGroup
