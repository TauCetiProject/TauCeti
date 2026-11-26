/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Gluing elements of localizations along a family generating the unit ideal

Let `B` be a commutative semiring and `(gᵢ)` a family of elements generating the unit ideal, so
that the basic open subsets `D(gᵢ)` cover `Spec B`. Elements `xᵢ ∈ B[1/gᵢ]` whose images in
every `B[1/(gᵢgⱼ)]` agree are the images of a unique element of `B`. This is the sheaf property
of the structure sheaf of `Spec B` for a cover by basic opens.

Mathlib states this as `Localization.existsUnique_algebraMap_eq_of_span_eq_top`, for the
localizations `Localization.Away a` at the elements `a` of a subset of `B`. Here the cover is an
arbitrary family, which may repeat elements, the localizations are arbitrary
`IsLocalization.Away` models, and the maps to `B[1/(gᵢgⱼ)]` are any ring homomorphisms compatible
with the maps from `B` (they are unique, for instance `IsLocalization.Away.awayToAwayRight`).
This is the form in which the sheaf property is met by a presheaf whose sections over the
members of a cover and over their pairwise intersections are only known to be localizations
of `B`.

The second statement is relative to a basic open `D(s)`: the members of the cover and their
pairwise intersections are `D(σᵢ)` and `D(σᵢσⱼ)` inside `D(s)`, and the rings involved are all
localizations of the same base ring. This is how the sections of a presheaf over rational
subsets of an adic spectrum arise for a discrete Huber ring.

## Main results

* `IsLocalization.Away.injective_of_mul_self`: a ring homomorphism `B[1/g] → B[1/(g · g)]`
  compatible with the maps from `B` is injective.
* `IsLocalization.Away.existsUnique_algebraMap_eq_of_span_eq_top`: compatible elements of the
  localizations `B[1/gᵢ]` come from a unique element of `B`.
* `IsLocalization.Away.existsUnique_forall_eq_of_span_eq_top`: if the `σᵢ` generate the unit
  ideal of `R[1/s]`, compatible elements of the localizations `R[1/σᵢ]` come from a unique element
  of `R[1/s]`.

## References

* [Stacks Project, Lemma 10.24.1 (Tag 00EJ)](https://stacks.math.columbia.edu/tag/00EJ).
-/

public section

namespace IsLocalization.Away

section Spec

variable {B : Type*} [CommSemiring B] {ι : Type*} {g : ι → B}
  {Bi : ι → Type*} [∀ i, CommSemiring (Bi i)] [∀ i, Algebra B (Bi i)]
  [∀ i, IsLocalization.Away (g i) (Bi i)]
  {Bij : ι → ι → Type*} [∀ i j, CommSemiring (Bij i j)] [∀ i j, Algebra B (Bij i j)]
  [∀ i j, IsLocalization.Away (g i * g j) (Bij i j)]

/-- A ring homomorphism `B[1/g] → B[1/(g · g)]` compatible with the maps from `B` is injective:
`g · g` is already invertible in `B[1/g]`, so both rings are localizations of `B` away from
`g · g`. -/
theorem injective_of_mul_self {g : B} {Bg Bgg : Type*} [CommSemiring Bg]
    [CommSemiring Bgg] [Algebra B Bg] [Algebra B Bgg] [IsLocalization.Away g Bg]
    [IsLocalization.Away (g * g) Bgg] {ρ : Bg →+* Bgg}
    (hρ : ∀ b, ρ (algebraMap B Bg b) = algebraMap B Bgg b) : Function.Injective ρ :=
  have := mul_of_isUnit (S := Bg) g g (algebraMap_isUnit g)
  (IsLocalization.bijective (.powers (g * g)) ρ (RingHom.ext hρ)).1

variable {ρl : ∀ i j, Bi i →+* Bij i j} {ρr : ∀ i j, Bi j →+* Bij i j}
  (hρl : ∀ i j b, ρl i j (algebraMap B (Bi i) b) = algebraMap B (Bij i j) b)
  (hρr : ∀ i j b, ρr i j (algebraMap B (Bi j) b) = algebraMap B (Bij i j) b)
include hρl hρr

/-- Members of a compatible family at two indices with the same element `g k = g i` determine each
other: an element of `B` mapping to `x k` maps to `x i`. -/
private theorem algebraMap_eq_of_eq {x : ∀ i, Bi i} (hx : ∀ i j, ρl i j (x i) = ρr i j (x j))
    {i k : ι} (hki : g k = g i) {b : B} (hb : algebraMap B (Bi k) b = x k) :
    algebraMap B (Bi i) b = x i := by
  have : IsLocalization.Away (g i * g i) (Bij i k) := by
    rw [← congrArg (g i * ·) hki]
    infer_instance
  refine injective_of_mul_self (g := g i) (Bg := Bi i) (Bgg := Bij i k) (hρl i k) ?_
  rw [hx, ← hb, hρl, hρr]

variable (hg : Ideal.span (Set.range g) = ⊤)
include hg

/-- **Gluing along a family generating the unit ideal.** Let `(gᵢ)` generate the unit ideal of
`B`, and let `xᵢ ∈ B[1/gᵢ]` have the same images in `B[1/(gᵢgⱼ)]` for all `i` and `j`, along
ring homomorphisms compatible with the maps from `B`. Then the `xᵢ` are the images of a unique
element of `B`. The family may be infinite and may repeat elements. -/
theorem existsUnique_algebraMap_eq_of_span_eq_top (x : ∀ i, Bi i)
    (hx : ∀ i j, ρl i j (x i) = ρr i j (x j)) :
    ∃! b : B, ∀ i, algebraMap B (Bi i) b = x i := by
  classical
  -- Index the members of the range of `g` by a chosen preimage.
  let s : Set B := Set.range g
  choose k hk using fun a : s ↦ a.property
  -- Ring homomorphisms between `B[1/g (k a)]` and `Localization.Away a` in both directions.
  have hu₁ (a : s) : IsUnit (algebraMap B (Localization.Away a.val) (g (k a))) :=
    hk a ▸ IsLocalization.Away.algebraMap_isUnit _
  have hu₂ (a : s) : IsUnit (algebraMap B (Bi (k a)) a.val) :=
    hk a ▸ IsLocalization.Away.algebraMap_isUnit _
  let φ (a : s) : Bi (k a) →+* Localization.Away a.val := IsLocalization.Away.lift _ (hu₁ a)
  let ψ (a : s) : Localization.Away a.val →+* Bi (k a) := IsLocalization.Away.lift _ (hu₂ a)
  have hφ (a : s) (b : B) : φ a (algebraMap B _ b) = algebraMap B _ b :=
    IsLocalization.Away.lift_eq _ _ b
  have hψφ (a : s) (y : Bi (k a)) : ψ a (φ a y) = y :=
    RingHom.congr_fun (f := (ψ a).comp (φ a)) (g := RingHom.id _) (IsLocalization.ringHom_ext
      (.powers (g (k a))) <|
      RingHom.ext fun b ↦ by simp [φ, ψ, IsLocalization.Away.lift_eq]) y
  -- The images `φ a (x (k a))` are compatible in the sense of Mathlib's statement for subsets.
  have hu₃ (a c : s) :
      IsUnit (algebraMap B (Localization.Away (a.val * c.val)) (g (k a) * g (k c))) :=
    hk a ▸ hk c ▸ IsLocalization.Away.algebraMap_isUnit _
  let θ (a c : s) : Bij (k a) (k c) →+* Localization.Away (a.val * c.val) :=
    IsLocalization.Away.lift _ (hu₃ a c)
  have hθ (a c : s) (b : B) : θ a c (algebraMap B _ b) = algebraMap B _ b :=
    IsLocalization.Away.lift_eq _ _ b
  have hleft (a c : s) (y : Bi (k a)) :
      IsLocalization.Away.awayToAwayRight a.val c.val (φ a y) = θ a c (ρl _ _ y) :=
    RingHom.congr_fun (f := (IsLocalization.Away.awayToAwayRight
      (P := Localization.Away (a.val * c.val)) a.val c.val).comp (φ a)) (g := (θ a c).comp (ρl _ _))
      (IsLocalization.ringHom_ext
      (.powers (g (k a))) <| RingHom.ext fun b ↦ by
        simp [hφ, hθ, hρl, IsLocalization.Away.awayToAwayRight_eq]) y
  have hright (a c : s) (y : Bi (k c)) :
      IsLocalization.Away.awayToAwayLeft c.val a.val (φ c y) = θ a c (ρr _ _ y) :=
    RingHom.congr_fun (f := (IsLocalization.Away.awayToAwayLeft
      (P := Localization.Away (a.val * c.val)) c.val a.val).comp (φ c)) (g := (θ a c).comp (ρr _ _))
      (IsLocalization.ringHom_ext
      (.powers (g (k c))) <| RingHom.ext fun b ↦ by
        simp [hφ, hθ, hρr, IsLocalization.Away.awayToAwayLeft_eq]) y
  obtain ⟨b, hb, hbu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top s hg
    (fun a ↦ φ a (x (k a))) fun a c ↦ by rw [hleft, hright, hx]
  -- `b` is a preimage of each chosen `x (k a)`, and so of every `x i` by compatibility.
  have hbk (a : s) : algebraMap B (Bi (k a)) b = x (k a) := by
    rw [← hψφ a (x (k a)), ← hb a]
    exact (IsLocalization.Away.lift_eq a.val (hu₂ a) b).symm
  refine ⟨b, fun i ↦ algebraMap_eq_of_eq hρl hρr hx (hk ⟨g i, i, rfl⟩) (hbk _),
    fun b' hb' ↦ hbu b' fun a ↦ ?_⟩
  rw [← hb' (k a), hφ]

end Spec

section BasicOpen

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S] {ι : Type*}
  {σ : ι → R}
  {Si : ι → Type*} [∀ i, CommSemiring (Si i)] [∀ i, Algebra R (Si i)]
  [∀ i, IsLocalization.Away (σ i) (Si i)]
  {Sij : ι → ι → Type*} [∀ i j, CommSemiring (Sij i j)] [∀ i j, Algebra R (Sij i j)]
  [∀ i j, IsLocalization.Away (σ i * σ j) (Sij i j)]

/-- **Gluing over a basic open.** Let `S = R[1/s]`, and let `(σᵢ)` be a family whose images
generate the unit ideal of `S`, so that the `D(σᵢ)` cover `D(s)` in `Spec R`. Let `Sᵢ = R[1/σᵢ]`
and `Sᵢⱼ = R[1/(σᵢσⱼ)]`, with ring homomorphisms `S → Sᵢ`, `Sᵢ → Sᵢⱼ` and `Sⱼ → Sᵢⱼ` compatible
with the maps from `R`. If `xᵢ ∈ Sᵢ` have the same images in every `Sᵢⱼ`, they are the images of
a unique element of `S`.

The case `s = 1` is `IsLocalization.Away.existsUnique_algebraMap_eq_of_span_eq_top`, which this
reduces to: since `s` becomes a unit in `Sᵢ`, the ring `Sᵢ` is also the localization of `S` away
from the image of `σᵢ`. -/
theorem existsUnique_forall_eq_of_span_eq_top (s : R) [IsLocalization.Away s S]
    (hσ : Ideal.span (Set.range fun i ↦ algebraMap R S (σ i)) = ⊤)
    {ρ : ∀ i, S →+* Si i} (hρ : ∀ i r, ρ i (algebraMap R S r) = algebraMap R (Si i) r)
    {ρl : ∀ i j, Si i →+* Sij i j} {ρr : ∀ i j, Si j →+* Sij i j}
    (hρl : ∀ i j r, ρl i j (algebraMap R (Si i) r) = algebraMap R (Sij i j) r)
    (hρr : ∀ i j r, ρr i j (algebraMap R (Si j) r) = algebraMap R (Sij i j) r)
    (x : ∀ i, Si i) (hx : ∀ i j, ρl i j (x i) = ρr i j (x j)) :
    ∃! b : S, ∀ i, ρ i b = x i := by
  classical
  let g (i : ι) : S := algebraMap R S (σ i)
  -- `s` is a unit in every `Si i` and every `Sij i j`, so these are localizations away from
  -- `s * σ i` and `s * (σ i * σ j)`, as are the localizations of `S` away from `g i` and
  -- `g i * g j`.
  have hs : IsUnit (algebraMap R S s) := IsLocalization.Away.algebraMap_isUnit s
  have hsi (i : ι) : IsUnit (algebraMap R (Si i) s) := by
    rw [← hρ]
    exact hs.map _
  have hsij (i j : ι) : IsUnit (algebraMap R (Sij i j) s) := by
    rw [← hρl, ← hρ]
    exact (hs.map _).map _
  have _ (i : ι) : IsLocalization.Away (s * σ i) (Si i) := mul_of_isUnit' _ _ (hsi i)
  have _ (i j : ι) : IsLocalization.Away (s * (σ i * σ j)) (Sij i j) :=
    mul_of_isUnit' _ _ (hsij i j)
  let Bi (i : ι) := Localization.Away (g i)
  let Bij (i j : ι) := Localization.Away (algebraMap R S (σ i * σ j))
  have _ (i j : ι) : IsLocalization.Away (g i * g j) (Bij i j) := by
    simp only [g, Bij, ← map_mul]
    infer_instance
  let ci (i : ι) : Si i ≃ₐ[R] Bi i := IsLocalization.algEquiv (.powers (s * σ i)) _ _
  let cij (i j : ι) : Sij i j ≃ₐ[R] Bij i j :=
    IsLocalization.algEquiv (.powers (s * (σ i * σ j))) _ _
  -- transport the family to the localizations `Bi i` of `S`
  have hc (i : ι) (b : S) : ci i (ρ i b) = algebraMap S (Bi i) b :=
    RingHom.congr_fun (f := (ci i : Si i →+* Bi i).comp (ρ i)) (IsLocalization.ringHom_ext
      (.powers s) <| RingHom.ext fun r ↦ by simp [hρ, ← IsScalarTower.algebraMap_apply]) b
  have hcl (i j : ι) (b : S) : cij i j (ρl i j (ρ i b)) = algebraMap S (Bij i j) b :=
    RingHom.congr_fun (f := (cij i j : Sij i j →+* Bij i j).comp ((ρl i j).comp (ρ i)))
      (IsLocalization.ringHom_ext (.powers s) <| RingHom.ext fun r ↦ by
        simp [hρ, hρl, ← IsScalarTower.algebraMap_apply]) b
  have hcr (i j : ι) (b : S) : cij i j (ρr i j (ρ j b)) = algebraMap S (Bij i j) b :=
    RingHom.congr_fun (f := (cij i j : Sij i j →+* Bij i j).comp ((ρr i j).comp (ρ j)))
      (IsLocalization.ringHom_ext (.powers s) <| RingHom.ext fun r ↦ by
        simp [hρ, hρr, ← IsScalarTower.algebraMap_apply]) b
  have hci (i : ι) (b : S) : (ci i).symm (algebraMap S (Bi i) b) = ρ i b := by
    rw [← hc, AlgEquiv.symm_apply_apply]
  obtain ⟨b, hb, hbu⟩ := existsUnique_algebraMap_eq_of_span_eq_top (Bi := Bi) (Bij := Bij)
    (ρl := fun i j ↦ (cij i j : Sij i j →+* Bij i j).comp ((ρl i j).comp (ci i).symm))
    (ρr := fun i j ↦ (cij i j : Sij i j →+* Bij i j).comp ((ρr i j).comp (ci j).symm))
    (fun i j b ↦ by simp [hci, hcl]) (fun i j b ↦ by simp [hci, hcr]) hσ
    (fun i ↦ ci i (x i)) fun i j ↦ by simp [hx]
  refine ⟨b, fun i ↦ (ci i).injective (by rw [hc, hb]), fun b' hb' ↦ hbu b' fun i ↦ ?_⟩
  rw [← hc, hb']

end BasicOpen

end IsLocalization.Away
