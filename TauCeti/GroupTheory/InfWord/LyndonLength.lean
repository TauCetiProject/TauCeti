/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.SetLike.Basic
public import TauCeti.GroupTheory.InfWord.CDR
public import TauCeti.GroupTheory.LyndonLength.Basic

/-!
# Free Lyndon length functions on subgroups of `CDR(Λ, X)`

Let `Λ` be a discretely ordered abelian group and `X` a set. Whenever a group `G` maps into
`InfWord Λ X` by a function `φ : G → InfWord Λ X` respecting the partial multiplication — that is,
`IsMul (φ g) (φ h) (φ (g * h))` for all `g, h : G` — the length function `g ↦ (φ g).length` is a
Lyndon length function (`TauCeti.InfWord.lyndonLength`) whose Gromov products lie in `Λ` and equal
the lengths of longest common initial segments (`TauCeti.InfWord.gromovProduct_lyndonLength`,
`TauCeti.InfWord.exists_coe_eq_gromovProduct_lyndonLength`). When `φ` is injective and lands in
`CDR Λ X`, axiom (L5) follows from `TauCeti.InfWord.length_lt_of_isMul_self_of_mem_CDR`, so the
induced length function is free (`TauCeti.InfWord.isFree_lyndonLength`).

Bundling subsets of `InfWord Λ X` that contain `empty Λ X`, are closed under inversion, and are
closed under totalized partial multiplication `∗` as `TauCeti.InfWord.WordSubgroup Λ X`, every
`H : WordSubgroup Λ X` is a group under `∗` and carries the Lyndon length function
`H.lyndonLength`. If `(H : Set (InfWord Λ X)) ⊆ CDR Λ X`, then `H.lyndonLength` is a free Lyndon
length function (`TauCeti.InfWord.length_isLyndon`), proving Corollary 4.2 of Myasnikov,
Remeslennikov, and Serbin.

## Main definitions

* `TauCeti.InfWord.lyndonLength`: the Lyndon length function `g ↦ (φ g).length` induced by a map
  `φ : G → InfWord Λ X` preserving partial multiplication.
* `TauCeti.InfWord.WordSubgroup`: a subset of `InfWord Λ X` forming a group under `∗`.
* `TauCeti.InfWord.WordSubgroup.lyndonLength`: word length `w ↦ |w|` as a Lyndon length function
  on a subgroup of reduced `Λ`-words.

## Main results

* `TauCeti.InfWord.min_le_of_isGreatest_commonPrefix`: the ultrametric inequality for longest
  common initial segments of infinite words.
* `TauCeti.InfWord.gromovProduct_lyndonLength`: the Gromov product `c(g, f)` equals the length of
  the longest common initial segment of `φ g` and `φ f`.
* `TauCeti.InfWord.isFree_lyndonLength`: an injective multiplication-preserving map into `CDR Λ X`
  induces a free Lyndon length function.
* `TauCeti.InfWord.length_isLyndon`: on any subgroup of `CDR Λ X`, word length `w ↦ |w|` is a free
  Lyndon length function.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §4, Theorem 4.1 and Corollary 4.2.
* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Groups with free regular length
  functions in `ℤⁿ`*, Trans. Amer. Math. Soc. 364 (2012), 2847–2882, §2.3, Theorem 2.
-/

public section

namespace TauCeti

namespace InfWord

variable {Λ X : Type*}

/-! ### Ultrametric inequality for longest common initial segments -/

section CommonPrefix

variable [Zero Λ] [LinearOrder Λ]

/-- The lengths of longest common initial segments of three `Λ`-words satisfy the ultrametric
inequality `min δ(u, v) δ(v, w) ≤ δ(u, w)`. -/
theorem min_le_of_isGreatest_commonPrefix {u v w : InfWord Λ X} {δ₁ δ₂ δ₃ : Λ}
    (h₁ : IsGreatest {β | 0 ≤ β ∧ β ≤ u.length ∧ β ≤ v.length ∧ u.take β = v.take β} δ₁)
    (h₂ : IsGreatest {β | 0 ≤ β ∧ β ≤ v.length ∧ β ≤ w.length ∧ v.take β = w.take β} δ₂)
    (h₃ : IsGreatest {β | 0 ≤ β ∧ β ≤ u.length ∧ β ≤ w.length ∧ u.take β = w.take β} δ₃) :
    min δ₁ δ₂ ≤ δ₃ := by
  refine h₃.2 ⟨le_min h₁.1.1 h₂.1.1, (min_le_left _ _).trans h₁.1.2.1,
    (min_le_right _ _).trans h₂.1.2.2.1, ?_⟩
  have h1 : u.take (min δ₁ δ₂) = v.take (min δ₁ δ₂) := by
    rw [min_comm, ← take_take, h₁.1.2.2.2, take_take]
  have h2 : v.take (min δ₁ δ₂) = w.take (min δ₁ δ₂) := by
    rw [← take_take, h₂.1.2.2.2, take_take]
  exact h1.trans h2

end CommonPrefix

variable [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]

/-! ### Lyndon length function induced by a map into infinite words -/

section Hom

variable {G : Type*} [Group G] (φ : G → InfWord Λ X)
  (hφ : ∀ g h, IsMul (φ g) (φ h) (φ (g * h)))

include hφ in
/-- Every value of a map respecting `IsMul` is a reduced word. -/
theorem isReduced_of_isMul (g : G) : (φ g).IsReduced :=
  (hφ g 1).isReduced_left

include hφ in
/-- A map from a group into `InfWord Λ X` respecting `IsMul` sends `1` to `empty Λ X`. -/
theorem map_one_of_isMul : φ 1 = empty Λ X := by
  have h1 : IsMul (φ 1) (φ 1) (φ 1) := by simpa using hφ 1 1
  exact h1.left_cancel (isMul_empty_right (isReduced_of_isMul φ hφ 1))

include hφ in
/-- A map from a group into `InfWord Λ X` respecting `IsMul` commutes with inversion. -/
theorem map_inv_of_isMul (g : G) : φ g⁻¹ = (φ g)⁻¹ := by
  have h1 : IsMul (φ g) (φ g⁻¹) (empty Λ X) := by
    rw [← map_one_of_isMul φ hφ, ← mul_inv_cancel g]
    exact hφ g g⁻¹
  exact (isMul_empty_iff.1 h1).2

include hφ in
/-- A map from a group into `InfWord Λ X` respecting `IsMul` is injective iff only `1` maps to
the empty word. -/
theorem injective_of_isMul_iff : Function.Injective φ ↔ ∀ g, φ g = empty Λ X → g = 1 := by
  refine ⟨fun hinj g hg => hinj (hg.trans (map_one_of_isMul φ hφ).symm), fun hker g h hgh => ?_⟩
  have hmul : IsMul (φ g)⁻¹ (φ g) (φ (g⁻¹ * h)) := by
    rw [← map_inv_of_isMul φ hφ, hgh]
    exact hφ g⁻¹ h
  have h1 : g⁻¹ * h = 1 := hker _ (isMul_inv_self_iff.1 hmul).2
  exact inv_mul_eq_one.1 h1

/-- The Lyndon length function `g ↦ (φ g).length` induced by a map `φ : G → InfWord Λ X`
respecting the partial multiplication `IsMul`. -/
def lyndonLength : LyndonLength G Λ where
  toFun g := (φ g).length
  map_one' := by rw [map_one_of_isMul φ hφ, length_empty]
  map_inv' g := by rw [map_inv_of_isMul φ hφ, length_inv]
  eq_of_lt' g f h hlt := by
    have hgf : IsMul (φ g)⁻¹ (φ f) (φ (g⁻¹ * f)) := map_inv_of_isMul φ hφ g ▸ hφ g⁻¹ f
    have hgh : IsMul (φ g)⁻¹ (φ h) (φ (g⁻¹ * h)) := map_inv_of_isMul φ hφ g ▸ hφ g⁻¹ h
    have hfh : IsMul (φ f)⁻¹ (φ h) (φ (f⁻¹ * h)) := map_inv_of_isMul φ hφ f ▸ hφ f⁻¹ h
    obtain ⟨δgf, hδgf⟩ := exists_isGreatest_of_isMul_inv_left hgf
    obtain ⟨δgh, hδgh⟩ := exists_isGreatest_of_isMul_inv_left hgh
    obtain ⟨δfh, hδfh⟩ := exists_isGreatest_of_isMul_inv_left hfh
    have egf := length_add_two_nsmul_eq_of_isMul_inv_left hgf hδgf
    have egh := length_add_two_nsmul_eq_of_isMul_inv_left hgh hδgh
    have efh := length_add_two_nsmul_eq_of_isMul_inv_left hfh hδfh
    have h₁ := min_le_of_isGreatest_commonPrefix hδgf hδfh hδgh
    have hδfg : IsGreatest {β | 0 ≤ β ∧ β ≤ (φ f).length ∧ β ≤ (φ g).length ∧
        (φ f).take β = (φ g).take β} δgf := by
      convert hδgf using 1
      ext β
      simp only [Set.mem_ofPred_eq, eq_comm]
      tauto
    have h₂ := min_le_of_isGreatest_commonPrefix hδfg hδgh hδfh
    have hδeq : δgh = δfh := by
      have hlt' : δgh < δgf := by
        simp only [two_nsmul] at egf egh
        grind
      grind
    simp only [hδeq, two_nsmul] at egh efh
    grind

/-- Evaluation of `InfWord.lyndonLength`. -/
@[simp]
theorem lyndonLength_apply (g : G) : lyndonLength φ hφ g = (φ g).length := (rfl)

/-- The Gromov product of `InfWord.lyndonLength` at `g, f` is the length of the longest common
initial segment of `φ g` and `φ f`. -/
theorem gromovProduct_lyndonLength {g f : G} {δ : Λ}
    (hδ : IsGreatest {β | 0 ≤ β ∧ β ≤ (φ g).length ∧ β ≤ (φ f).length ∧
      (φ g).take β = (φ f).take β} δ) :
    (lyndonLength φ hφ).gromovProduct g f = (δ : DivisibleHull Λ) := by
  rw [eq_comm, LyndonLength.coe_eq_gromovProduct_iff]
  have hgf : IsMul (φ g)⁻¹ (φ f) (φ (g⁻¹ * f)) := map_inv_of_isMul φ hφ g ▸ hφ g⁻¹ f
  have eq := length_add_two_nsmul_eq_of_isMul_inv_left hgf hδ
  simp only [lyndonLength_apply, two_nsmul] at eq ⊢
  grind

/-- Axiom (L4) for `InfWord.lyndonLength`: every Gromov product lies in `Λ`. -/
theorem exists_coe_eq_gromovProduct_lyndonLength (g f : G) :
    ∃ c : Λ, (c : DivisibleHull Λ) = (lyndonLength φ hφ).gromovProduct g f := by
  have hgf : IsMul (φ g)⁻¹ (φ f) (φ (g⁻¹ * f)) := map_inv_of_isMul φ hφ g ▸ hφ g⁻¹ f
  obtain ⟨δ, hδ⟩ := exists_isGreatest_of_isMul_inv_left hgf
  exact ⟨δ, (gromovProduct_lyndonLength φ hφ hδ).symm⟩

/-- An injective map `φ : G → InfWord Λ X` respecting `IsMul` and taking values in `CDR Λ X`
induces a free Lyndon length function on `G`. -/
theorem isFree_lyndonLength (hφ_inj : Function.Injective φ) (hCDR : ∀ g, φ g ∈ CDR Λ X) :
    (lyndonLength φ hφ).IsFree where
  exists_coe_eq_gromovProduct := exists_coe_eq_gromovProduct_lyndonLength φ hφ
  lt_map_sq g hg := by
    have hne : φ g ≠ empty Λ X := fun h =>
      hg (hφ_inj (h.trans (map_one_of_isMul φ hφ).symm))
    have hsq : IsMul (φ g) (φ g) (φ (g ^ 2)) := by
      simpa [pow_two] using hφ g g
    exact length_lt_of_isMul_self_of_mem_CDR (hCDR g) hne hsq

end Hom

/-! ### Subgroups of reduced infinite words -/

/-- A *subgroup of reduced `Λ`-words*: a set of `Λ`-words containing the empty word, closed under
inversion, and closed under totalized partial multiplication `∗`. Every element is automatically
reduced (`TauCeti.InfWord.WordSubgroup.isReduced_of_mem`), and the carrier forms a group under
`∗`. -/
structure WordSubgroup (Λ X : Type*) [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
    [SuccOrder Λ] where
  /-- The underlying set of reduced `Λ`-words. -/
  carrier : Set (InfWord Λ X)
  /-- The empty word belongs to the subgroup. -/
  empty_mem' : empty Λ X ∈ carrier
  /-- Closure under inversion. -/
  inv_mem' : ∀ {w}, w ∈ carrier → w⁻¹ ∈ carrier
  /-- Closure under defined partial multiplication `∗`. -/
  mul_mem' : ∀ {u v}, u ∈ carrier → v ∈ carrier → ∃ w ∈ carrier, IsMul u v w

namespace WordSubgroup

instance : SetLike (WordSubgroup Λ X) (InfWord Λ X) where
  coe := carrier
  coe_injective H₁ H₂ h := by
    cases H₁
    cases H₂
    congr

/-- Two subgroups of reduced `Λ`-words are equal iff they contain the same words. -/
@[ext]
theorem ext {H₁ H₂ : WordSubgroup Λ X} (h : ∀ w, w ∈ H₁ ↔ w ∈ H₂) : H₁ = H₂ :=
  SetLike.ext h

variable {H : WordSubgroup Λ X} {u v w : InfWord Λ X}

/-- The empty word belongs to every subgroup of reduced `Λ`-words. -/
@[simp]
theorem empty_mem (H : WordSubgroup Λ X) : empty Λ X ∈ H :=
  H.empty_mem'

/-- A subgroup of reduced `Λ`-words is closed under inversion. -/
theorem inv_mem (hu : u ∈ H) : u⁻¹ ∈ H :=
  H.inv_mem' hu

/-- Membership in a subgroup of reduced `Λ`-words is invariant under inversion. -/
@[simp]
theorem inv_mem_iff : u⁻¹ ∈ H ↔ u ∈ H :=
  ⟨fun h => by simpa using inv_mem h, inv_mem⟩

/-- The partial product `u ∗ v` of two words in `H` is defined and lies in `H`. -/
theorem mul_mem (hu : u ∈ H) (hv : v ∈ H) : ∃ w ∈ H, IsMul u v w :=
  H.mul_mem' hu hv

/-- Every word in a `WordSubgroup` is reduced. -/
theorem isReduced_of_mem (hu : u ∈ H) : u.IsReduced := by
  obtain ⟨_, -, hmul⟩ := H.mul_mem hu H.empty_mem
  exact hmul.isReduced_left

/-- If `u, v ∈ H` and `IsMul u v w`, then `w ∈ H`. -/
theorem mem_of_isMul (hu : u ∈ H) (hv : v ∈ H) (h : IsMul u v w) : w ∈ H := by
  obtain ⟨w', hw', h'⟩ := H.mul_mem hu hv
  rwa [h.unique h']

/-- A subgroup of reduced `Λ`-words is a group under the partial multiplication `∗`. -/
noncomputable instance instGroup (H : WordSubgroup Λ X) : Group H where
  one := ⟨empty Λ X, H.empty_mem⟩
  inv u := ⟨u.1⁻¹, H.inv_mem u.2⟩
  mul u v := ⟨(H.mul_mem u.2 v.2).choose, (H.mul_mem u.2 v.2).choose_spec.1⟩
  mul_assoc u v w := by
    have huv : IsMul u.1 v.1 (H.mul_mem u.2 v.2).choose := (H.mul_mem u.2 v.2).choose_spec.2
    have hvw : IsMul v.1 w.1 (H.mul_mem v.2 w.2).choose := (H.mul_mem v.2 w.2).choose_spec.2
    have h1 := (H.mul_mem (H.mul_mem u.2 v.2).choose_spec.1 w.2).choose_spec.2
    have h2 := (H.mul_mem u.2 (H.mul_mem v.2 w.2).choose_spec.1).choose_spec.2
    exact Subtype.ext ((huv.assoc_left hvw h1).unique h2)
  one_mul u := Subtype.ext ((H.mul_mem H.empty_mem u.2).choose_spec.2.unique
    (isMul_empty_left (H.isReduced_of_mem u.2)))
  mul_one u := Subtype.ext ((H.mul_mem u.2 H.empty_mem).choose_spec.2.unique
    (isMul_empty_right (H.isReduced_of_mem u.2)))
  inv_mul_cancel u := Subtype.ext ((H.mul_mem (H.inv_mem u.2) u.2).choose_spec.2.unique
    (isMul_inv_self (H.isReduced_of_mem u.2)))

/-- The identity element of `H` is the empty word. -/
@[simp]
theorem coe_one (H : WordSubgroup Λ X) : ((1 : H) : InfWord Λ X) = empty Λ X := (rfl)

/-- Inversion in `H` is word inversion. -/
@[simp]
theorem coe_inv (u : H) : ((u⁻¹ : H) : InfWord Λ X) = (u : InfWord Λ X)⁻¹ := (rfl)

/-- Multiplication in `H` satisfies the relation `IsMul`. -/
theorem isMul_mul (u v : H) :
    IsMul (u : InfWord Λ X) (v : InfWord Λ X) ((u * v : H) : InfWord Λ X) :=
  (H.mul_mem u.2 v.2).choose_spec.2

/-- Multiplication in `H` agrees with the partial product `InfWord.mul`. -/
theorem mul_eq_some (u v : H) :
    (u : InfWord Λ X).mul (v : InfWord Λ X) = Part.some ((u * v : H) : InfWord Λ X) :=
  mul_eq_some_iff.2 (isMul_mul u v)

/-- Characterization of multiplication in `H` in terms of `IsMul`. -/
theorem mul_eq_iff (u v w : H) :
    u * v = w ↔ IsMul (u : InfWord Λ X) (v : InfWord Λ X) (w : InfWord Λ X) :=
  ⟨fun h => h ▸ isMul_mul u v, fun h => Subtype.ext ((isMul_mul u v).unique h)⟩

/-- Word length `w ↦ |w|` as a Lyndon length function on a subgroup `H` of reduced `Λ`-words. -/
noncomputable def lyndonLength (H : WordSubgroup Λ X) : LyndonLength H Λ :=
  InfWord.lyndonLength Subtype.val isMul_mul

/-- Evaluation of `WordSubgroup.lyndonLength`. -/
@[simp]
theorem lyndonLength_apply (H : WordSubgroup Λ X) (u : H) :
    H.lyndonLength u = (u : InfWord Λ X).length := (rfl)

/-- The Gromov product of `WordSubgroup.lyndonLength` at `u, v : H` is the length of the longest
common initial segment of `u` and `v`. -/
theorem gromovProduct_lyndonLength {u v : H} {δ : Λ}
    (hδ : IsGreatest {β | 0 ≤ β ∧ β ≤ (u : InfWord Λ X).length ∧ β ≤ (v : InfWord Λ X).length ∧
      (u : InfWord Λ X).take β = (v : InfWord Λ X).take β} δ) :
    H.lyndonLength.gromovProduct u v = (δ : DivisibleHull Λ) :=
  InfWord.gromovProduct_lyndonLength Subtype.val isMul_mul hδ

end WordSubgroup

/-- On any subgroup of `CDR Λ X`, word length `w ↦ |w|` is a free Lyndon length function
(Myasnikov–Remeslennikov–Serbin, Corollary 4.2). -/
theorem length_isLyndon (H : WordSubgroup Λ X) (hH : (H : Set (InfWord Λ X)) ⊆ CDR Λ X) :
    H.lyndonLength.IsFree :=
  isFree_lyndonLength Subtype.val WordSubgroup.isMul_mul Subtype.val_injective fun u => hH u.2

end InfWord

end TauCeti
