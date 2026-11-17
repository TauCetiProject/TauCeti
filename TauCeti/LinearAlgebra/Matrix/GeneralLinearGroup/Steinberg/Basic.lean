/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.PresentedGroup
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Steinberg groups

For an arbitrary associative ring `R` and an index type `ι`, the **Steinberg group** `St_ι(R)` is
the group presented by generators `x_{ij}(a)` (`i ≠ j` in `ι`, `a ∈ R`) subject to the Steinberg
relations:
1. additivity `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)`;
2. distant commutation `[x_{ij}(a), x_{kl}(b)] = 1` whenever `j ≠ k` and `i ≠ l`;
3. the Chevalley commutator relation `[x_{ij}(a), x_{jk}(b)] = x_{ik}(a b)` for distinct `i, j, k`.

The reversed commutator identity `[x_{ij}(a), x_{ki}(b)] = x_{kj}(-(b a))` follows from the third
relation by taking inverses. Taking `ι = Fin n` gives the finite Steinberg groups `Stₙ(R)`, and
taking `ι = ℕ` gives the stable Steinberg group `St(R)`, which is canonically isomorphic to the
direct limit `colim_n Stₙ(R)` along the stabilization maps `Stₘ(R) →* Stₙ(R)`.

When every pair of distinct indices admits a third distinct index—in particular whenever `ι` is
finite of cardinality at least `3` or infinite—the Steinberg group `St_ι(R)` is perfect, since
`x_{ij}(a) = [x_{ik}(a), x_{kj}(1)]`. For `ι = Fin 2` there are no triples of distinct indices and
no distant commutation between the opposite roots `(0, 1)` and `(1, 0)`, so `St₂(R)` is the free
product of two copies of the additive group of `R`.

For finite `ι`, sending `x_{ij}(a)` to the transvection `1 + a E_{ij}` defines a homomorphism
`St_ι(R) →* GL ι R` whose image is the elementary subgroup `E_ι(R)`.

## Main definitions

* `TauCeti.steinbergRelations`: the defining relations of `St_ι(R)` inside the free group on
  distinct index pairs times `R`.
* `TauCeti.SteinbergGroup`: the Steinberg group `St_ι(R)` as a `PresentedGroup`.
* `TauCeti.SteinbergGroup.of`, `TauCeti.SteinbergGroup.ofHom`: the Steinberg generators `x_{ij}(a)`
  and their one-parameter root subgroups `Multiplicative R →* St_ι(R)`.
* `TauCeti.SteinbergGroup.lift`: the universal property of `St_ι(R)`.
* `TauCeti.SteinbergGroup.mapRing`: functoriality in ring homomorphisms `R →+* S`.
* `TauCeti.SteinbergGroup.mapIndex`, `TauCeti.SteinbergGroup.reindex`: functoriality in injective
  index maps and equivalences.
* `TauCeti.SteinbergGroup.stabilize`, `TauCeti.SteinbergGroup.toStable`,
  `TauCeti.SteinbergGroup.directLimitEquiv`: stabilization maps `Stₘ(R) →* Stₙ(R)`, canonical maps
  `Stₙ(R) →* St(R)`, and the direct-limit isomorphism `colim_n Stₙ(R) ≃* St(R)`.
* `TauCeti.SteinbergGroup.toGL`, `TauCeti.SteinbergGroup.toElementary`: the canonical homomorphism
  `St_ι(R) →* GL ι R` and its corestriction onto `E_ι(R)`.
* `TauCeti.SteinbergGroup.equivCoprodFinTwo`: the free-product identification
  `St₂(R) ≃* Multiplicative R ∗ Multiplicative R`.

## Main results

* `TauCeti.SteinbergGroup.of_add`, `TauCeti.SteinbergGroup.of_zero`,
  `TauCeti.SteinbergGroup.of_inv`, `TauCeti.SteinbergGroup.commute_of`,
  `TauCeti.SteinbergGroup.commutatorElement_of`,
  `TauCeti.SteinbergGroup.commutatorElement_of_reverse`: the Steinberg relations.
* `TauCeti.SteinbergGroup.isPerfect_of_exists_ne`,
  `TauCeti.SteinbergGroup.isPerfect_of_three_le_card`: perfectness of `St_ι(R)` when at least three
  indices are available.
* `TauCeti.SteinbergGroup.exists_toStable`: every element of `St(R)` lies in the image of `Stₙ(R)`
  for some `n`.
* `TauCeti.SteinbergGroup.range_toGL`, `TauCeti.SteinbergGroup.toElementary_surjective`: the image
  of `St_ι(R) →* GL ι R` is the elementary subgroup `E_ι(R)`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72, Princeton
  University Press (1971), §5.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5.1.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

/-! ## Definition and basic relations -/

/-- The defining relations of the Steinberg group `St_ι(R)` on the generators `x_{ij}(a)` for
distinct `i, j : ι` and `a : R`:
1. additivity `x_{ij}(a) x_{ij}(b) = x_{ij}(a + b)`;
2. distant commutation `[x_{ij}(a), x_{kl}(b)] = 1` when `j ≠ k` and `i ≠ l`;
3. the Chevalley commutator relation `[x_{ij}(a), x_{jk}(b)] = x_{ik}(a * b)` for distinct
   `i, j, k`.

Commutators follow the convention `[x, y] = x y x⁻¹ y⁻¹`. -/
def steinbergRelations (ι : Type*) (R : Type*) [Ring R] :
    Set (FreeGroup ({p : ι × ι // p.1 ≠ p.2} × R)) :=
  {r | (∃ (p : {p : ι × ι // p.1 ≠ p.2}) (a b : R),
          r = FreeGroup.of (p, a) * FreeGroup.of (p, b) * (FreeGroup.of (p, a + b))⁻¹) ∨
       (∃ (p q : {p : ι × ι // p.1 ≠ p.2}) (a b : R), p.1.2 ≠ q.1.1 ∧ p.1.1 ≠ q.1.2 ∧
          r = ⁅FreeGroup.of (p, a), FreeGroup.of (q, b)⁆) ∨
       (∃ (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
          r = ⁅FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a),
               FreeGroup.of ((⟨(j, k), hjk⟩ : {p : ι × ι // p.1 ≠ p.2}), b)⁆ *
            (FreeGroup.of ((⟨(i, k), hik⟩ : {p : ι × ι // p.1 ≠ p.2}), a * b))⁻¹)}

/-- The **Steinberg group** `St_ι(R)` over an associative ring `R` indexed by `ι`, presented by the
generators `x_{ij}(a)` (`i ≠ j`) and the Steinberg relations `TauCeti.steinbergRelations ι R`.
Taking `ι = Fin n` gives `Stₙ(R)`, and taking `ι = ℕ` gives the stable Steinberg group `St(R)`. -/
abbrev SteinbergGroup (ι : Type*) (R : Type*) [Ring R] :=
  PresentedGroup (steinbergRelations ι R)

namespace SteinbergGroup

section Basic

variable {ι : Type*} {R : Type*} [Ring R]

/-- The Steinberg generator `x_{ij}(a)` in `St_ι(R)` for distinct indices `i ≠ j` and `a : R`. -/
def of {i j : ι} (hij : i ≠ j) (a : R) : SteinbergGroup ι R :=
  PresentedGroup.of (⟨(i, j), hij⟩, a)

/-- The parameter of a Steinberg generator is additive: `x_{ij}(a + b) = x_{ij}(a) x_{ij}(b)`. -/
@[simp]
theorem of_add {i j : ι} (hij : i ≠ j) (a b : R) :
    of hij (a + b) = of hij a * of hij b := by
  have hmem :
      FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a) *
          FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), b) *
          (FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a + b))⁻¹ ∈
        steinbergRelations ι R :=
    Or.inl ⟨⟨(i, j), hij⟩, a, b, rfl⟩
  exact (PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem).symm

/-- The Steinberg generator of parameter zero is the identity: `x_{ij}(0) = 1`. -/
@[simp]
theorem of_zero {i j : ι} (hij : i ≠ j) : of hij (0 : R) = 1 := by
  have h : of hij (0 : R) * of hij (0 : R) = of hij 0 := by
    rw [← of_add, add_zero]
  simpa using h

/-- The inverse of a Steinberg generator negates its parameter: `x_{ij}(a)⁻¹ = x_{ij}(-a)`. -/
@[simp]
theorem of_inv {i j : ι} (hij : i ≠ j) (a : R) : (of hij a)⁻¹ = of hij (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← of_add, add_neg_cancel, of_zero]

/-- The one-parameter root subgroup `Multiplicative R →* St_ι(R)` attached to a pair of distinct
indices `i ≠ j`. -/
def ofHom {i j : ι} (hij : i ≠ j) : Multiplicative R →* SteinbergGroup ι R where
  toFun a := of hij a.toAdd
  map_one' := of_zero hij
  map_mul' a b := of_add hij a.toAdd b.toAdd

/-- Evaluating `ofHom` at `a` gives the Steinberg generator `x_{ij}(a.toAdd)`. -/
@[simp]
theorem ofHom_apply {i j : ι} (hij : i ≠ j) (a : Multiplicative R) :
    ofHom hij a = of hij a.toAdd :=
  (rfl)

/-- Distant Steinberg generators commute: `[x_{ij}(a), x_{kl}(b)] = 1` when `j ≠ k` and `i ≠ l`. -/
theorem commute_of {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l)
    (a b : R) : Commute (of hij a) (of hkl b) := by
  have hmem :
      ⁅FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a),
       FreeGroup.of ((⟨(k, l), hkl⟩ : {p : ι × ι // p.1 ≠ p.2}), b)⁆ ∈
        steinbergRelations ι R :=
    Or.inr (Or.inl ⟨⟨(i, j), hij⟩, ⟨(k, l), hkl⟩, a, b, hjk, hil, rfl⟩)
  exact commutatorElement_eq_one_iff_commute.mp <| by
    simpa [of, PresentedGroup.of] using PresentedGroup.one_of_mem hmem

/-- The Chevalley commutator relation in `St_ι(R)`: `[x_{ij}(a), x_{jk}(b)] = x_{ik}(a * b)` for
distinct `i, j, k`. -/
theorem commutatorElement_of {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅of hij a, of hjk b⁆ = of hik (a * b) := by
  have hmem :
      ⁅FreeGroup.of ((⟨(i, j), hij⟩ : {p : ι × ι // p.1 ≠ p.2}), a),
       FreeGroup.of ((⟨(j, k), hjk⟩ : {p : ι × ι // p.1 ≠ p.2}), b)⁆ *
        (FreeGroup.of ((⟨(i, k), hik⟩ : {p : ι × ι // p.1 ≠ p.2}), a * b))⁻¹ ∈
        steinbergRelations ι R :=
    Or.inr (Or.inr ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩)
  simpa [of, PresentedGroup.of] using PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem

/-- The reverse-orientation Chevalley commutator relation in `St_ι(R)`:
`[x_{ij}(a), x_{ki}(b)] = x_{kj}(-(b * a))` for distinct `i, j, k`. -/
theorem commutatorElement_of_reverse {i j k : ι} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (a b : R) : ⁅of hij a, of hki b⁆ = of hkj (-(b * a)) := by
  calc
    ⁅of hij a, of hki b⁆ = ⁅of hki b, of hij a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = (of hkj (b * a))⁻¹ := by rw [commutatorElement_of hki hij hkj]
    _ = of hkj (-(b * a)) := of_inv hkj (b * a)

/-- A subgroup of `St_ι(R)` containing all Steinberg generators `x_{ij}(a)` is the whole group. -/
theorem generated_by (H : Subgroup (SteinbergGroup ι R))
    (h : ∀ (i j : ι) (hij : i ≠ j) (a : R), of hij a ∈ H) (x : SteinbergGroup ι R) : x ∈ H :=
  PresentedGroup.generated_by (steinbergRelations ι R) H (fun ⟨⟨⟨i, j⟩, hij⟩, a⟩ ↦ h i j hij a) x

/-- Two monoid homomorphisms out of `St_ι(R)` agree as soon as they agree on every Steinberg
generator `x_{ij}(a)`. -/
@[ext]
theorem hom_ext {M : Type*} [Monoid M] {φ ψ : SteinbergGroup ι R →* M}
    (h : ∀ (i j : ι) (hij : i ≠ j) (a : R), φ (of hij a) = ψ (of hij a)) : φ = ψ := by
  ext x
  have hunit : φ.toHomUnits = ψ.toHomUnits :=
    PresentedGroup.ext fun ⟨⟨⟨i, j⟩, hij⟩, a⟩ ↦ Units.ext (h i j hij a)
  exact congrArg Units.val (DFunLike.congr_fun hunit x)

/-- The **universal property of `St_ι(R)`**: any family of elements `f i j hij a` in a group `G`
satisfying the Steinberg relations extends uniquely to a homomorphism `St_ι(R) →* G`. -/
def lift {G : Type*} [Group G] (f : ∀ (i j : ι), i ≠ j → R → G)
    (hadd : ∀ (i j : ι) (hij : i ≠ j) (a b : R), f i j hij a * f i j hij b = f i j hij (a + b))
    (hcomm : ∀ (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → i ≠ l → ∀ a b,
      Commute (f i j hij a) (f k l hkl b))
    (hchevalley : ∀ (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f i j hij a, f j k hjk b⁆ = f i k hik (a * b)) :
    SteinbergGroup ι R →* G :=
  PresentedGroup.toGroup
    (f := fun x : {p : ι × ι // p.1 ≠ p.2} × R ↦ f x.1.1.1 x.1.1.2 x.1.2 x.2) <| by
      intro r hr
      rcases hr with ⟨⟨⟨i, j⟩, hij⟩, a, b, rfl⟩ |
        ⟨⟨⟨i, j⟩, hij⟩, ⟨⟨k, l⟩, hkl⟩, a, b, hjk, hil, rfl⟩ |
        ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩
      · simp [hadd i j hij a b]
      · simpa [commutatorElement_eq_one_iff_commute] using hcomm i j k l hij hkl hjk hil a b
      · simp [hchevalley i j k hij hjk hik a b]

/-- The homomorphism induced by a Steinberg family sends `x_{ij}(a)` to `f i j hij a`. -/
@[simp]
theorem lift_of {G : Type*} [Group G] {f : ∀ (i j : ι), i ≠ j → R → G}
    {hadd : ∀ (i j : ι) (hij : i ≠ j) (a b : R), f i j hij a * f i j hij b = f i j hij (a + b)}
    {hcomm : ∀ (i j k l : ι) (hij : i ≠ j) (hkl : k ≠ l), j ≠ k → i ≠ l → ∀ a b,
      Commute (f i j hij a) (f k l hkl b)}
    {hchevalley : ∀ (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R),
      ⁅f i j hij a, f j k hjk b⁆ = f i k hik (a * b)}
    {i j : ι} (hij : i ≠ j) (a : R) :
    lift f hadd hcomm hchevalley (of hij a) = f i j hij a :=
  PresentedGroup.toGroup.of _

/-- Over a subsingleton ring every Steinberg generator vanishes, so `St_ι(R)` is trivial. -/
instance [Subsingleton R] : Subsingleton (SteinbergGroup ι R) := by
  refine subsingleton_of_forall_eq 1 fun x ↦ ?_
  exact generated_by ⊥ (fun _ _ hij a ↦ by rw [Subsingleton.elim a 0, of_zero]; rfl) x

/-- Over a subsingleton index type there are no generators, so `St_ι(R)` is trivial. -/
instance [Subsingleton ι] : Subsingleton (SteinbergGroup ι R) := by
  refine subsingleton_of_forall_eq 1 fun x ↦ ?_
  exact generated_by ⊥ (fun i j hij _ ↦ (hij (Subsingleton.elim i j)).elim) x

/-- **Perfectness of `St_ι(R)`.** Whenever every pair of distinct indices admits a third distinct
index, every generator `x_{ij}(a) = [x_{ik}(a), x_{kj}(1)]` is a commutator, so `St_ι(R)` is
perfect. -/
theorem isPerfect_of_exists_ne (hι : ∀ i j : ι, i ≠ j → ∃ k : ι, k ≠ i ∧ k ≠ j) :
    Group.IsPerfect (SteinbergGroup ι R) := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro x _
  refine generated_by (commutator (SteinbergGroup ι R)) (fun i j hij a ↦ ?_) x
  obtain ⟨k, hki, hkj⟩ := hι i j hij
  have heq : of hij a = ⁅of hki.symm a, of hkj (1 : R)⁆ := by
    rw [commutatorElement_of hki.symm hkj hij, mul_one]
  rw [heq]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- For a finite index type of cardinality at least `3`, `St_ι(R)` is perfect. -/
theorem isPerfect_of_three_le_card [Fintype ι] (hι : 3 ≤ Fintype.card ι) :
    Group.IsPerfect (SteinbergGroup ι R) := by
  classical
  refine isPerfect_of_exists_ne fun i j _ ↦ ?_
  have hlt : ({i, j} : Finset ι).card < (Finset.univ : Finset ι).card :=
    lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega)
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨k, by simpa [not_or] using hk⟩

/-- For an infinite index type—in particular `ι = ℕ`—the Steinberg group `St_ι(R)` is perfect. -/
instance [Infinite ι] : Group.IsPerfect (SteinbergGroup ι R) :=
  isPerfect_of_exists_ne fun i j _ ↦ by
    obtain ⟨k, hk⟩ := Set.infinite_univ.exists_notMem_finite (Set.toFinite ({i, j} : Set ι))
    exact ⟨k, by simpa [not_or] using hk⟩

end Basic

/-! ## Functoriality in rings and index types -/

section Functoriality

variable {ι κ μ : Type*} {R S T : Type*} [Ring R] [Ring S] [Ring T]

/-- The homomorphism `St_ι(R) →* St_ι(S)` induced by a ring homomorphism `f : R →+* S`, sending
`x_{ij}(a)` to `x_{ij}(f a)`. -/
def mapRing (f : R →+* S) : SteinbergGroup ι R →* SteinbergGroup ι S :=
  lift (fun _ _ hij a ↦ of hij (f a))
    (fun _ _ hij a b ↦ by rw [← of_add, map_add])
    (fun _ _ _ _ hij hkl hjk hil a b ↦ commute_of hij hkl hjk hil (f a) (f b))
    (fun _ _ _ hij hjk hik a b ↦ by rw [commutatorElement_of hij hjk hik, map_mul])

/-- `mapRing f` sends `x_{ij}(a)` to `x_{ij}(f a)`. -/
@[simp]
theorem mapRing_of (f : R →+* S) {i j : ι} (hij : i ≠ j) (a : R) :
    mapRing f (of hij a) = of hij (f a) :=
  lift_of ..

/-- The identity ring homomorphism induces the identity on `St_ι(R)`. -/
@[simp]
theorem mapRing_id : mapRing (ι := ι) (RingHom.id R) = MonoidHom.id (SteinbergGroup ι R) := by
  ext i j hij a
  simp

/-- `mapRing` is functorial in ring homomorphisms. -/
theorem mapRing_comp (f : R →+* S) (g : S →+* T) :
    mapRing (ι := ι) (g.comp f) = (mapRing g).comp (mapRing f) := by
  ext i j hij a
  simp

/-- Applying `mapRing f` followed by `mapRing g` is applying `mapRing (g.comp f)`. -/
@[simp]
theorem mapRing_mapRing (f : R →+* S) (g : S →+* T) (x : SteinbergGroup ι R) :
    mapRing g (mapRing f x) = mapRing (g.comp f) x := by
  rw [mapRing_comp, MonoidHom.comp_apply]

/-- A surjective ring homomorphism induces a surjective homomorphism of Steinberg groups. -/
theorem mapRing_surjective {f : R →+* S} (hf : Function.Surjective f) :
    Function.Surjective (mapRing (ι := ι) f) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro y _
  refine generated_by (mapRing f).range (fun i j hij b ↦ ?_) y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨of hij a, mapRing_of f hij a⟩

/-- The homomorphism `St_ι(R) →* St_κ(R)` induced by an injective map of index types `σ : ι → κ`,
sending `x_{ij}(a)` to `x_{σ i, σ j}(a)`. -/
def mapIndex {σ : ι → κ} (hσ : Function.Injective σ) : SteinbergGroup ι R →* SteinbergGroup κ R :=
  lift (fun _ _ hij a ↦ of (hσ.ne hij) a)
    (fun _ _ hij a b ↦ (of_add (hσ.ne hij) a b).symm)
    (fun _ _ _ _ hij hkl hjk hil a b ↦
      commute_of (hσ.ne hij) (hσ.ne hkl) (hσ.ne hjk) (hσ.ne hil) a b)
    (fun _ _ _ hij hjk hik a b ↦ commutatorElement_of (hσ.ne hij) (hσ.ne hjk) (hσ.ne hik) a b)

/-- `mapIndex hσ` sends `x_{ij}(a)` to `x_{σ i, σ j}(a)`. -/
@[simp]
theorem mapIndex_of {σ : ι → κ} (hσ : Function.Injective σ) {i j : ι} (hij : i ≠ j) (a : R) :
    mapIndex (R := R) hσ (of hij a) = of (hσ.ne hij) a :=
  lift_of ..

/-- The identity index map induces the identity on `St_ι(R)`. -/
@[simp]
theorem mapIndex_id :
    mapIndex (R := R) (Function.injective_id (α := ι)) = MonoidHom.id (SteinbergGroup ι R) := by
  ext i j hij a
  simp

/-- `mapIndex` is functorial in injective index maps. -/
theorem mapIndex_comp {σ : ι → κ} {τ : κ → μ} (hσ : Function.Injective σ)
    (hτ : Function.Injective τ) :
    mapIndex (R := R) (hτ.comp hσ) = (mapIndex hτ).comp (mapIndex hσ) := by
  ext i j hij a
  simp

/-- Ring homomorphisms and injective index maps commute on Steinberg groups. -/
theorem mapRing_comp_mapIndex (f : R →+* S) {σ : ι → κ} (hσ : Function.Injective σ) :
    (mapRing f).comp (mapIndex hσ) = (mapIndex hσ).comp (mapRing f) := by
  ext i j hij a
  simp

/-- Reindexing along a bijection `e : ι ≃ κ` gives an isomorphism `St_ι(R) ≃* St_κ(R)`. -/
def reindex (e : ι ≃ κ) : SteinbergGroup ι R ≃* SteinbergGroup κ R :=
  MonoidHom.toMulEquiv (mapIndex e.injective) (mapIndex e.symm.injective)
    (by ext i j hij a; simp)
    (by ext i j hij a; simp)

/-- `reindex e` sends `x_{ij}(a)` to `x_{e i, e j}(a)`. -/
@[simp]
theorem reindex_of (e : ι ≃ κ) {i j : ι} (hij : i ≠ j) (a : R) :
    reindex (R := R) e (of hij a) = of (e.injective.ne hij) a :=
  mapIndex_of e.injective hij a

/-- The inverse of `reindex e` sends `x_{ij}(a)` to `x_{e.symm i, e.symm j}(a)`. -/
@[simp]
theorem reindex_symm_of (e : ι ≃ κ) {i j : κ} (hij : i ≠ j) (a : R) :
    (reindex (R := R) e).symm (of hij a) = of (e.symm.injective.ne hij) a :=
  mapIndex_of e.symm.injective hij a

end Functoriality

/-! ## Stabilization and the direct-limit identification `colim Stₙ(R) ≃* St(R)` -/

section Stabilization

variable (R : Type*) [Ring R]

/-- The stabilization homomorphism `Stₘ(R) →* Stₙ(R)` for `m ≤ n`, induced by `Fin.castLE`. -/
def stabilize {m n : ℕ} (h : m ≤ n) : SteinbergGroup (Fin m) R →* SteinbergGroup (Fin n) R :=
  mapIndex (Fin.castLE_injective h)

variable {R}

/-- Stabilization preserves generator parameters while casting indices via `Fin.castLE`. -/
@[simp]
theorem stabilize_of {m n : ℕ} (h : m ≤ n) {i j : Fin m} (hij : i ≠ j) (a : R) :
    stabilize R h (of hij a) = of ((Fin.castLE_injective h).ne hij) a :=
  mapIndex_of ..

/-- Stabilization to the same size is the identity. -/
@[simp]
theorem stabilize_refl (n : ℕ) :
    stabilize R (le_refl n) = MonoidHom.id (SteinbergGroup (Fin n) R) := by
  ext i j hij a
  simp

/-- Stabilizations compose. -/
@[simp]
theorem stabilize_stabilize {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n)
    (x : SteinbergGroup (Fin k) R) :
    stabilize R hmn (stabilize R hkm x) = stabilize R (hkm.trans hmn) x := by
  have h : (stabilize R hmn).comp (stabilize R hkm) = stabilize R (hkm.trans hmn) := by
    ext i j hij a
    simp
  exact DFunLike.congr_fun h x

/-- The finite Steinberg groups `Stₙ(R)` with `stabilize` form a directed system of groups. -/
instance : DirectedSystem (fun n : ℕ ↦ SteinbergGroup (Fin n) R) fun _ _ h ↦ stabilize R h where
  map_self x := by simp
  map_map _ _ _ hkm hmn x := stabilize_stabilize hkm hmn x

variable (R) in
/-- The canonical homomorphism `Stₙ(R) →* St(R)` induced by `Fin.val : Fin n → ℕ`. -/
def toStable (n : ℕ) : SteinbergGroup (Fin n) R →* SteinbergGroup ℕ R :=
  mapIndex Fin.val_injective

/-- `toStable n` sends `x_{ij}(a)` to `x_{(i : ℕ), (j : ℕ)}(a)`. -/
@[simp]
theorem toStable_of {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : R) :
    toStable R n (of hij a) = of (Fin.val_injective.ne hij) a :=
  mapIndex_of ..

/-- The canonical maps `Stₙ(R) →* St(R)` are compatible with stabilization. -/
@[simp]
theorem toStable_stabilize {m n : ℕ} (h : m ≤ n) (x : SteinbergGroup (Fin m) R) :
    toStable R n (stabilize R h x) = toStable R m x := by
  have hcomp : (toStable R n).comp (stabilize R h) = toStable R m := by
    ext i j hij a
    simp
  exact DFunLike.congr_fun hcomp x

/-- Every element of the stable Steinberg group `St(R)` lies in the image of `Stₙ(R)` for some
`n`. -/
theorem exists_toStable (x : SteinbergGroup ℕ R) :
    ∃ (n : ℕ) (y : SteinbergGroup (Fin n) R), toStable R n y = x := by
  let H : Subgroup (SteinbergGroup ℕ R) := ⨆ n : ℕ, (toStable R n).range
  have hx : x ∈ H := by
    refine generated_by H (fun i j hij a ↦ ?_) x
    refine Subgroup.mem_iSup_of_mem (max i j + 1) ?_
    refine ⟨of (i := (⟨i, by omega⟩ : Fin (max i j + 1))) (j := ⟨j, by omega⟩)
      (by simpa [Fin.ext_iff] using hij) a, ?_⟩
    simp
  have hdir : Directed (· ≤ ·) fun n : ℕ ↦ (toStable R n).range := by
    intro m n
    refine ⟨max m n, ?_, ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨stabilize R (le_max_left m n) y, toStable_stabilize _ y⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨stabilize R (le_max_right m n) y, toStable_stabilize _ y⟩
  rw [Subgroup.mem_iSup_of_directed hdir] at hx
  obtain ⟨n, y, rfl⟩ := hx
  exact ⟨n, y, rfl⟩

/-- The image of a Steinberg generator in `colim_n Stₙ(R)`, formed at stage `max i j + 1`. -/
private def directLimitGen {i j : ℕ} (hij : i ≠ j) (a : R) :
    DirectLimit (fun n : ℕ ↦ SteinbergGroup (Fin n) R) (fun _ _ h ↦ stabilize R h) :=
  DirectLimit.Monoid.of (fun n : ℕ ↦ SteinbergGroup (Fin n) R) (fun _ _ h ↦ stabilize R h)
    (max i j + 1)
    (of (i := (⟨i, by omega⟩ : Fin (max i j + 1))) (j := ⟨j, by omega⟩)
      (by simpa [Fin.ext_iff] using hij) a)

private theorem directLimitGen_eq_of {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) (a : R) :
    directLimitGen hij a =
      DirectLimit.Monoid.of (fun n : ℕ ↦ SteinbergGroup (Fin n) R) (fun _ _ h ↦ stabilize R h) n
        (of (i := (⟨i, hi⟩ : Fin n)) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff] using hij) a) := by
  have hle : max i j + 1 ≤ n := by omega
  rw [directLimitGen, ← DirectLimit.Monoid.of_f
    (G := fun n : ℕ ↦ SteinbergGroup (Fin n) R) (f := fun _ _ h ↦ stabilize R h) hle,
    stabilize_of]

variable (R) in
/-- **Direct-limit identification of the stable Steinberg group:** `colim_n Stₙ(R) ≃* St(R)`. -/
def directLimitEquiv :
    DirectLimit (fun n : ℕ ↦ SteinbergGroup (Fin n) R) (fun _ _ h ↦ stabilize R h) ≃*
      SteinbergGroup ℕ R :=
  MonoidHom.toMulEquiv
    (DirectLimit.Monoid.lift _ (fun _ _ h ↦ stabilize R h) (toStable R)
      (fun _ _ h x ↦ toStable_stabilize h x))
    (lift (fun _ _ hij a ↦ directLimitGen hij a)
      (fun _ _ hij a b ↦ by rw [directLimitGen, directLimitGen, directLimitGen, ← map_mul, of_add])
      (fun i j k l hij hkl hjk hil a b ↦ by
        let n := max (max i j) (max k l) + 1
        rw [directLimitGen_eq_of (n := n) (by omega) (by omega) hij a,
          directLimitGen_eq_of (n := n) (by omega) (by omega) hkl b]
        exact (commute_of (i := (⟨i, by omega⟩ : Fin n)) (j := ⟨j, by omega⟩)
          (k := ⟨k, by omega⟩) (l := ⟨l, by omega⟩) (by simpa [Fin.ext_iff] using hij)
          (by simpa [Fin.ext_iff] using hkl) (by simpa [Fin.ext_iff] using hjk)
          (by simpa [Fin.ext_iff] using hil) a b).map _)
      (fun i j k hij hjk hik a b ↦ by
        let n := max (max i j) k + 1
        rw [directLimitGen_eq_of (n := n) (by omega) (by omega) hij a,
          directLimitGen_eq_of (n := n) (by omega) (by omega) hjk b,
          directLimitGen_eq_of (n := n) (by omega) (by omega) hik (a * b),
          ← map_commutatorElement]
        exact congrArg _ (commutatorElement_of (i := (⟨i, by omega⟩ : Fin n)) (j := ⟨j, by omega⟩)
          (k := ⟨k, by omega⟩) (by simpa [Fin.ext_iff] using hij)
          (by simpa [Fin.ext_iff] using hjk) (by simpa [Fin.ext_iff] using hik) a b)))
    (DirectLimit.Monoid.hom_ext fun n ↦ hom_ext fun i j hij a ↦ by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, DirectLimit.Monoid.lift_of, toStable_of,
        lift_of]
      exact directLimitGen_eq_of i.isLt j.isLt (Fin.val_injective.ne hij) a)
    (hom_ext fun i j hij a ↦ by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, lift_of, directLimitGen,
        DirectLimit.Monoid.lift_of, toStable_of])

/-- The direct-limit isomorphism sends the class of `x ∈ Stₙ(R)` to `toStable R n x`. -/
@[simp]
theorem directLimitEquiv_mk (n : ℕ) (x : SteinbergGroup (Fin n) R) :
    directLimitEquiv R ⟦⟨n, x⟩⟧ = toStable R n x :=
  DirectLimit.Monoid.lift_mk ..

/-- The direct-limit isomorphism restricts on component `n` to `toStable R n`. -/
theorem directLimitEquiv_of (n : ℕ) (x : SteinbergGroup (Fin n) R) :
    directLimitEquiv R
      (DirectLimit.Monoid.of (fun n : ℕ ↦ SteinbergGroup (Fin n) R)
        (fun _ _ h ↦ stabilize R h) n x) =
      toStable R n x :=
  DirectLimit.Monoid.lift_of ..

/-- The inverse of the direct-limit isomorphism sends `x_{ij}(a)` to the class of `x_{ij}(a)` in
component `n` for any `n` strictly larger than both `i` and `j`. -/
theorem directLimitEquiv_symm_of {n i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) (a : R) :
    (directLimitEquiv R).symm (of hij a) =
      DirectLimit.Monoid.of (fun n : ℕ ↦ SteinbergGroup (Fin n) R) (fun _ _ h ↦ stabilize R h) n
        (of (i := (⟨i, hi⟩ : Fin n)) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff] using hij) a) := by
  rw [directLimitEquiv, MonoidHom.toMulEquiv_symm_apply, lift_of]
  exact directLimitGen_eq_of hi hj hij a

end Stabilization

/-! ## Canonical map to `GL` and `E` -/

section ToGL

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R S : Type*} [Ring R] [Ring S]

variable (ι R) in
/-- The canonical homomorphism `St_ι(R) →* GL ι R` sending `x_{ij}(a)` to the transvection
`1 + a E_{ij}`. -/
def toGL : SteinbergGroup ι R →* GL ι R :=
  lift (fun _ _ hij a ↦ transvectionUnit hij a)
    (fun _ _ hij a b ↦ (transvectionUnit_add hij a b).symm)
    (fun _ _ _ _ hij hkl hjk hil a b ↦ commute_transvectionUnit hij hkl hjk hil.symm a b)
    (fun _ _ _ hij hjk hik a b ↦ commutatorElement_transvectionUnit hij hjk hik a b)

/-- `toGL` sends the generator `x_{ij}(a)` to `transvectionUnit hij a`. -/
@[simp]
theorem toGL_of {i j : ι} (hij : i ≠ j) (a : R) :
    toGL ι R (of hij a) = transvectionUnit hij a :=
  lift_of ..

/-- The image of `toGL : St_ι(R) →* GL ι R` is the elementary subgroup `E_ι(R)`. -/
@[simp]
theorem range_toGL : (toGL ι R).range = elementarySubgroup ι R := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact generated_by ((elementarySubgroup ι R).comap (toGL ι R))
      (fun _ _ hij a ↦ by simp [transvectionUnit_mem_elementarySubgroup]) x
  · exact elementarySubgroup_le_iff.2 fun _ _ hij a ↦ ⟨of hij a, toGL_of hij a⟩

variable (ι R) in
/-- The canonical surjective homomorphism `St_ι(R) →* E_ι(R)`. -/
def toElementary : SteinbergGroup ι R →* elementarySubgroup ι R :=
  (toGL ι R).codRestrict (elementarySubgroup ι R) fun x ↦ range_toGL (ι := ι) (R := R) ▸ ⟨x, rfl⟩

/-- Composing `toElementary` with the subgroup inclusion recovers `toGL`. -/
@[simp]
theorem coe_toElementary (x : SteinbergGroup ι R) :
    (toElementary ι R x : GL ι R) = toGL ι R x :=
  (rfl)

/-- The homomorphism `St_ι(R) →* E_ι(R)` is surjective. -/
theorem toElementary_surjective : Function.Surjective (toElementary ι R) := by
  rintro ⟨g, hg⟩
  rw [← range_toGL] at hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨x, Subtype.ext rfl⟩

/-- `toGL` is natural in ring homomorphisms. -/
theorem toGL_mapRing (f : R →+* S) (x : SteinbergGroup ι R) :
    toGL ι S (mapRing f x) = Units.map (f.mapMatrix (m := ι)).toMonoidHom (toGL ι R x) := by
  have h : (toGL ι S).comp (mapRing f) =
      (Units.map (f.mapMatrix (m := ι)).toMonoidHom).comp (toGL ι R) := by
    ext i j hij a
    simp [RingHom.unitsMap_mapMatrix_transvectionUnit]
  exact DFunLike.congr_fun h x

/-- `toGL` is compatible with reindexing along an equivalence `e : ι ≃ κ`. -/
theorem toGL_reindex (e : ι ≃ κ) (x : SteinbergGroup ι R) :
    toGL κ R (reindex e x) = e.reindexGL R (toGL ι R x) := by
  have h : (toGL κ R).comp (reindex e).toMonoidHom =
      (e.reindexGL R).toMonoidHom.comp (toGL ι R) := by
    ext i j hij a
    simp [Equiv.reindexGL_transvectionUnit]
  exact DFunLike.congr_fun h x

/-- `toGL` is compatible with stabilization `Stₘ(R) →* Stₙ(R)`. -/
theorem toGL_stabilize {m n : ℕ} (h : m ≤ n) (x : SteinbergGroup (Fin m) R) :
    toGL (Fin n) R (stabilize R h x) = stabilizeGL R h (toGL (Fin m) R x) := by
  have hcomp : (toGL (Fin n) R).comp (stabilize R h) =
      (stabilizeGL R h).comp (toGL (Fin m) R) := by
    ext i j hij a
    simp [stabilizeGL_transvectionUnit]
  exact DFunLike.congr_fun hcomp x

end ToGL

/-! ## The rank-two Steinberg group `St₂(R)` -/

section FinTwo

variable (R : Type*) [Ring R]

/-- `St₂(R)` is the free product of two copies of the additive group of `R`: with only two indices
there are no Chevalley commutator relations and no distant commutation between the opposite roots
`(0, 1)` and `(1, 0)`. -/
def equivCoprodFinTwo :
    SteinbergGroup (Fin 2) R ≃* Monoid.Coprod (Multiplicative R) (Multiplicative R) :=
  MonoidHom.toMulEquiv
    (lift (fun i _ _ a ↦ if i = 0 then Monoid.Coprod.inl (Multiplicative.ofAdd a)
        else Monoid.Coprod.inr (Multiplicative.ofAdd a))
      (fun i _ _ a b ↦ by split_ifs <;> simp [← map_mul])
      (fun i j k l hij hkl hjk hil a b ↦ by
        have hik : i = k := by fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
          simp_all
        subst hik
        split_ifs
        · exact (Commute.all _ _).map Monoid.Coprod.inl
        · exact (Commute.all _ _).map Monoid.Coprod.inr)
      (fun i j k hij hjk hik _ _ ↦ by
        exfalso; fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all))
    (Monoid.Coprod.lift (ofHom (show (0 : Fin 2) ≠ 1 by decide))
      (ofHom (show (1 : Fin 2) ≠ 0 by decide)))
    (hom_ext fun i j hij a ↦ by
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · simp
      · simp
      · exact (hij rfl).elim)
    (Monoid.Coprod.hom_ext
      (MonoidHom.ext fun a ↦ by simp)
      (MonoidHom.ext fun a ↦ by simp))

/-- `equivCoprodFinTwo` sends `x₀₁(a)` to the left copy of `a`. -/
@[simp]
theorem equivCoprodFinTwo_of_zero_one (a : R) :
    equivCoprodFinTwo R (of (show (0 : Fin 2) ≠ 1 by decide) a) =
      Monoid.Coprod.inl (Multiplicative.ofAdd a) := by
  simp [equivCoprodFinTwo]

/-- `equivCoprodFinTwo` sends `x₁₀(a)` to the right copy of `a`. -/
@[simp]
theorem equivCoprodFinTwo_of_one_zero (a : R) :
    equivCoprodFinTwo R (of (show (1 : Fin 2) ≠ 0 by decide) a) =
      Monoid.Coprod.inr (Multiplicative.ofAdd a) := by
  simp [equivCoprodFinTwo]

/-- The inverse of `equivCoprodFinTwo` sends the left copy of `a` to `x₀₁(a)`. -/
@[simp]
theorem equivCoprodFinTwo_symm_inl (a : Multiplicative R) :
    (equivCoprodFinTwo R).symm (Monoid.Coprod.inl a) =
      of (show (0 : Fin 2) ≠ 1 by decide) a.toAdd := by
  simp [equivCoprodFinTwo]

/-- The inverse of `equivCoprodFinTwo` sends the right copy of `a` to `x₁₀(a)`. -/
@[simp]
theorem equivCoprodFinTwo_symm_inr (a : Multiplicative R) :
    (equivCoprodFinTwo R).symm (Monoid.Coprod.inr a) =
      of (show (1 : Fin 2) ≠ 0 by decide) a.toAdd := by
  simp [equivCoprodFinTwo]

end FinTwo

end SteinbergGroup

end TauCeti
