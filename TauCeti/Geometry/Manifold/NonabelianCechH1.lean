/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Nonabelian Čech `H¹` of a cover with coefficients in a Lie group

Let `G` be a `C^n` Lie group modelled on `IG` and let `U : ι → Set B` be a family of subsets of a
manifold `B` modelled on `IB`. A family `c i j : B → G` is a `C^n` cocycle on `U`
(`TauCeti.IsContMDiffGroupCocycle`) when `c j k * c i j = c i k` on the triple overlaps and each
`c i j` is `C^n` on `U i ∩ U j`; this is the convention of `TauCeti.fiberBundleCoreOfGroupCocycle`,
in which `c i j` carries fibre coordinates of chart `i` to fibre coordinates of chart `j`. Two
families are `C^n`-cohomologous (`TauCeti.IsContMDiffCohomologous`) when
`c' i j = (h j)⁻¹ * c i j * h i` on the overlaps for a `0`-cochain `h` with each `h i` of class
`C^n` on `U i`. In terms of local sections `s i` of a principal bundle with `s j = s i • g i j`,
where `g i j = c j i`, this is the change of transition functions under `s i ↦ s i • h i`.

The **nonabelian Čech `H¹`** of the cover, `TauCeti.NonabelianCechH1 IB IG n G U`, is the set of
`C^n` cocycles modulo this equivalence relation. It is a pointed set, with base point the class of
the constant cocycle `1`, and a class is the base point exactly when its cocycles are coboundaries
`(h j)⁻¹ * h i` (`TauCeti.NonabelianCechH1.mk_eq_one_iff`). A refinement `V k ⊆ U (τ k)` induces
the refinement map `TauCeti.NonabelianCechH1.refine τ`, which restricts cocycles along `τ`. It
preserves the base point, is functorial for the identity and for composite refinements, and does
not depend on the choice of `τ` (`TauCeti.NonabelianCechH1.refine_eq_refine`), because two choices
differ by the coboundary of the transitions `c (τ' k) (τ k)` between the chosen charts.

Mathlib's `CategoryTheory.PresheafOfGroups.H1` is the corresponding set for a presheaf of groups on
a category, whose `1`-cochains are compatible families of sections over every object mapping to
two members of the cover. Here cochains are functions `B → G` on a cover by arbitrary subsets,
`C^n` for any `n`, which is the form in which `TauCeti.fiberBundleCoreOfGroupCocycle` and
`TauCeti.diffeomorphOfCohomologous` consume them.

The classification of principal bundles by this set is in
`TauCeti.Geometry.Manifold.FiberBundle.Principal.Classification`.

## Main definitions

* `TauCeti.IsContMDiffGroupCocycle`: `C^n` group-valued cocycles on a cover.
* `TauCeti.IsContMDiffCohomologous`: cocycles differing by a `C^n` `0`-cochain.
* `TauCeti.NonabelianCechH1`: the nonabelian Čech `H¹` of a cover, with
  `TauCeti.NonabelianCechH1.refine` its refinement maps.

## References

* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer, 1966, §3.1 (the nonabelian
  first Čech cohomology set of a covering and its refinement maps).
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB}
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] {HG : Type*} [TopologicalSpace HG]
  {IG : ModelWithCorners 𝕜 EG HG} {n : ℕ∞ω}
  {ι κ ν B G : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G] [ChartedSpace HG G]

/-! ### Cocycles and cohomologous cocycles -/

variable (IB IG n) in
/-- A family `c i j : B → G` is a `C^n` cocycle on the cover `U` when it satisfies the cocycle
condition `c j k b * c i j b = c i k b` on the triple overlaps and each `c i j` is `C^n` on the
overlap `U i ∩ U j`. This is the composition convention of
`TauCeti.fiberBundleCoreOfGroupCocycle`: `c i j` carries fibre coordinates of chart `i` to fibre
coordinates of chart `j`. The values of `c i j` off `U i ∩ U j` are irrelevant. -/
structure IsContMDiffGroupCocycle (U : ι → Set B) (c : ι → ι → B → G) : Prop where
  mul_eq : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c j k b * c i j b = c i k b
  contMDiffOn : ∀ i j, ContMDiffOn IB IG n (c i j) (U i ∩ U j)

variable (IB IG n) in
/-- Two families `c c' : ι → ι → B → G` are `C^n`-cohomologous on the cover `U` when
`c' i j = (h j)⁻¹ * c i j * h i` on every overlap `U i ∩ U j`, for some `0`-cochain `h` with each
`h i` of class `C^n` on `U i`. This is how the transition functions change when the local sections
of chart `i` are multiplied by `h i`. -/
def IsContMDiffCohomologous (U : ι → Set B) (c c' : ι → ι → B → G) : Prop :=
  ∃ h : ι → B → G, (∀ i, ContMDiffOn IB IG n (h i) (U i)) ∧
    ∀ i j b, b ∈ U i ∩ U j → c' i j b = (h j b)⁻¹ * c i j b * h i b

/-- Unfolding `TauCeti.IsContMDiffCohomologous`: the families are related by a `C^n` `0`-cochain. -/
theorem isContMDiffCohomologous_iff {U : ι → Set B} {c c' : ι → ι → B → G} :
    IsContMDiffCohomologous IB IG n U c c' ↔ ∃ h : ι → B → G,
      (∀ i, ContMDiffOn IB IG n (h i) (U i)) ∧
        ∀ i j b, b ∈ U i ∩ U j → c' i j b = (h j b)⁻¹ * c i j b * h i b :=
  Iff.rfl

namespace IsContMDiffGroupCocycle

variable {U : ι → Set B} {c : ι → ι → B → G}

/-- The constant cocycle `1`. -/
theorem one : IsContMDiffGroupCocycle IB IG n U fun _ _ _ ↦ (1 : G) :=
  ⟨fun _ _ _ _ _ ↦ mul_one 1, fun _ _ ↦ contMDiffOn_const⟩

/-- The `C^n` cocycle `c` is continuous on the overlaps. -/
theorem continuousOn (hc : IsContMDiffGroupCocycle IB IG n U c) (i j : ι) :
    ContinuousOn (c i j) (U i ∩ U j) :=
  (hc.contMDiffOn i j).continuousOn

/-- On a triple overlap, `c i j` is the transition from `i` to `j` through a third chart `a`. -/
theorem eq_mul_inv (hc : IsContMDiffGroupCocycle IB IG n U c) {a i j : ι} {b : B}
    (hb : b ∈ U a ∩ U i ∩ U j) : c i j b = c a j b * (c a i b)⁻¹ :=
  eq_mul_inv_of_mul_eq (hc.mul_eq a i j b hb)

/-- Restricting a cocycle along a refinement `V k ⊆ U (τ k)` gives a cocycle on `V`. -/
theorem comp (hc : IsContMDiffGroupCocycle IB IG n U c) {V : κ → Set B} (τ : κ → ι)
    (hτ : ∀ k, V k ⊆ U (τ k)) :
    IsContMDiffGroupCocycle IB IG n V fun k l ↦ c (τ k) (τ l) where
  mul_eq k l m b hb := hc.mul_eq _ _ _ b ⟨⟨hτ k hb.1.1, hτ l hb.1.2⟩, hτ m hb.2⟩
  contMDiffOn k l := (hc.contMDiffOn _ _).mono (inter_subset_inter (hτ k) (hτ l))

end IsContMDiffGroupCocycle

namespace IsContMDiffCohomologous

variable {U : ι → Set B} {c c' c'' : ι → ι → B → G}

/-- Families that agree on every overlap are cohomologous, through the constant cochain `1`. -/
theorem of_eqOn (h : ∀ i j, EqOn (c i j) (c' i j) (U i ∩ U j)) :
    IsContMDiffCohomologous IB IG n U c c' :=
  ⟨fun _ _ ↦ 1, fun _ ↦ contMDiffOn_const, fun i j b hb ↦ by simp [h i j hb]⟩

/-- Every family is cohomologous to itself. -/
@[refl]
theorem refl (c : ι → ι → B → G) : IsContMDiffCohomologous IB IG n U c c :=
  of_eqOn fun _ _ ↦ eqOn_refl _ _

/-- Being cohomologous is symmetric, through the inverse cochain. -/
theorem symm [LieGroup IG n G] (h : IsContMDiffCohomologous IB IG n U c c') :
    IsContMDiffCohomologous IB IG n U c' c := by
  obtain ⟨h, hh, hcc'⟩ := h
  refine ⟨fun i b ↦ (h i b)⁻¹, fun i ↦ (hh i).inv, fun i j b hb ↦ ?_⟩
  simp [hcc' i j b hb, mul_assoc]

/-- Being cohomologous is transitive, through the product of the cochains. -/
theorem trans [LieGroup IG n G] (h : IsContMDiffCohomologous IB IG n U c c')
    (h' : IsContMDiffCohomologous IB IG n U c' c'') :
    IsContMDiffCohomologous IB IG n U c c'' := by
  obtain ⟨h, hh, hcc'⟩ := h
  obtain ⟨h', hh', hc'c''⟩ := h'
  refine ⟨fun i b ↦ h i b * h' i b, fun i ↦ (hh i).mul (hh' i), fun i j b hb ↦ ?_⟩
  simp [hc'c'' i j b hb, hcc' i j b hb, mul_assoc]

/-- Restricting cohomologous families along a refinement `V k ⊆ U (τ k)` gives cohomologous
families on `V`, through the restricted cochain `h ∘ τ`. -/
theorem comp (h : IsContMDiffCohomologous IB IG n U c c') {V : κ → Set B} (τ : κ → ι)
    (hτ : ∀ k, V k ⊆ U (τ k)) :
    IsContMDiffCohomologous IB IG n V (fun k l ↦ c (τ k) (τ l)) fun k l ↦ c' (τ k) (τ l) := by
  obtain ⟨h, hh, hcc'⟩ := h
  exact ⟨fun k ↦ h (τ k), fun k ↦ (hh (τ k)).mono (hτ k), fun k l b hb ↦
    hcc' _ _ b ⟨hτ k hb.1, hτ l hb.2⟩⟩

end IsContMDiffCohomologous

/-- Two refinement maps `τ τ' : κ → ι` of `V` into `U` restrict a cocycle to cohomologous
cocycles on `V`, through the cochain `k ↦ c (τ' k) (τ k)` of transitions between the two chosen
charts. -/
theorem IsContMDiffGroupCocycle.isContMDiffCohomologous_comp {U : ι → Set B} {c : ι → ι → B → G}
    (hc : IsContMDiffGroupCocycle IB IG n U c)
    {V : κ → Set B} (τ τ' : κ → ι) (hτ : ∀ k, V k ⊆ U (τ k)) (hτ' : ∀ k, V k ⊆ U (τ' k)) :
    IsContMDiffCohomologous IB IG n V (fun k l ↦ c (τ k) (τ l)) fun k l ↦ c (τ' k) (τ' l) := by
  refine ⟨fun k ↦ c (τ' k) (τ k), fun k ↦ (hc.contMDiffOn _ _).mono fun b hb ↦
    ⟨hτ' k hb, hτ k hb⟩, fun k l b hb ↦ ?_⟩
  have hk := hτ k hb.1
  have hk' := hτ' k hb.1
  have hl := hτ l hb.2
  have hl' := hτ' l hb.2
  rw [mul_assoc, hc.mul_eq _ _ _ b ⟨⟨hk', hk⟩, hl⟩]
  exact eq_inv_mul_of_mul_eq (hc.mul_eq _ _ _ b ⟨⟨hk', hl'⟩, hl⟩)

/-! ### Nonabelian Čech `H¹` -/

variable (IB IG n G) in
/-- The relation of being `C^n`-cohomologous, on the `C^n` cocycles of the cover `U`. -/
def contMDiffCohomologousSetoid [LieGroup IG n G] (U : ι → Set B) :
    Setoid {c : ι → ι → B → G // IsContMDiffGroupCocycle IB IG n U c} where
  r c c' := IsContMDiffCohomologous IB IG n U c.1 c'.1
  iseqv := ⟨fun c ↦ .refl c.1, .symm, .trans⟩

variable (IB IG n G) in
/-- The **nonabelian Čech `H¹`** of the cover `U` with coefficients in the `C^n` functions to the
Lie group `G`: the `C^n` cocycles of `U` modulo the relation of being `C^n`-cohomologous. It is a
pointed set, with base point the class of the constant cocycle `1`
(`TauCeti.NonabelianCechH1.instOne`). -/
def NonabelianCechH1 [LieGroup IG n G] (U : ι → Set B) : Type _ :=
  Quotient (contMDiffCohomologousSetoid IB IG n G U)

namespace NonabelianCechH1

variable [LieGroup IG n G] {U : ι → Set B} {V : κ → Set B} {W : ν → Set B}

/-- The class of a `C^n` cocycle in the nonabelian Čech `H¹`. -/
def mk (c : ι → ι → B → G) (hc : IsContMDiffGroupCocycle IB IG n U c) :
    NonabelianCechH1 IB IG n G U :=
  Quotient.mk _ ⟨c, hc⟩

/-- Two cocycles have the same class exactly when they are cohomologous. -/
theorem mk_eq_mk_iff {c c' : ι → ι → B → G} {hc : IsContMDiffGroupCocycle IB IG n U c}
    {hc' : IsContMDiffGroupCocycle IB IG n U c'} :
    mk c hc = mk c' hc' ↔ IsContMDiffCohomologous IB IG n U c c' :=
  Quotient.eq

/-- Every class is the class of a cocycle. -/
@[elab_as_elim]
theorem ind {motive : NonabelianCechH1 IB IG n G U → Prop}
    (mk : ∀ c hc, motive (mk c hc)) (x : NonabelianCechH1 IB IG n G U) : motive x :=
  Quotient.ind (fun c ↦ mk c.1 c.2) x

/-- The base point of the nonabelian Čech `H¹`: the class of the constant cocycle `1`. -/
instance instOne : One (NonabelianCechH1 IB IG n G U) :=
  ⟨mk (fun _ _ _ ↦ 1) .one⟩

/-- The base point is the class of the constant cocycle `1`. -/
theorem one_def : (1 : NonabelianCechH1 IB IG n G U) = mk (fun _ _ _ ↦ 1) .one :=
  (rfl)

/-- A cocycle has trivial class exactly when it is a coboundary: `c i j = (h j)⁻¹ * h i` on the
overlaps for a `C^n` `0`-cochain `h`. -/
theorem mk_eq_one_iff {c : ι → ι → B → G} {hc : IsContMDiffGroupCocycle IB IG n U c} :
    mk c hc = 1 ↔ ∃ h : ι → B → G, (∀ i, ContMDiffOn IB IG n (h i) (U i)) ∧
      ∀ i j b, b ∈ U i ∩ U j → c i j b = (h j b)⁻¹ * h i b := by
  rw [one_def, mk_eq_mk_iff]
  constructor
  · intro hcoh
    obtain ⟨h, hh, h1c⟩ := hcoh.symm
    exact ⟨h, hh, fun i j b hb ↦ by simpa using h1c i j b hb⟩
  · rintro ⟨h, hh, hch⟩
    exact IsContMDiffCohomologous.symm ⟨h, hh, fun i j b hb ↦ by simpa using hch i j b hb⟩

/-- The **refinement map** of nonabelian Čech `H¹` along a refinement `V k ⊆ U (τ k)`: it restricts
a cocycle `c` on `U` to the cocycle `(k, l) ↦ c (τ k) (τ l)` on `V`. By
`TauCeti.NonabelianCechH1.refine_eq_refine` it does not depend on the choice of `τ`. -/
def refine (τ : κ → ι) (hτ : ∀ k, V k ⊆ U (τ k)) :
    NonabelianCechH1 IB IG n G U → NonabelianCechH1 IB IG n G V :=
  Quotient.map (fun c ↦ ⟨fun k l ↦ c.1 (τ k) (τ l), c.2.comp τ hτ⟩) fun _ _ h ↦ h.comp τ hτ

@[simp]
theorem refine_mk (τ : κ → ι) (hτ : ∀ k, V k ⊆ U (τ k)) (c : ι → ι → B → G)
    (hc : IsContMDiffGroupCocycle IB IG n U c) :
    refine τ hτ (mk c hc) = mk (fun k l ↦ c (τ k) (τ l)) (hc.comp τ hτ) :=
  (rfl)

/-- Refinement maps preserve the base point. -/
@[simp]
theorem refine_one (τ : κ → ι) (hτ : ∀ k, V k ⊆ U (τ k)) :
    refine τ hτ (1 : NonabelianCechH1 IB IG n G U) = 1 :=
  (rfl)

/-- The refinement map along the identity of a cover is the identity. -/
@[simp]
theorem refine_id (x : NonabelianCechH1 IB IG n G U) :
    refine id (fun _ ↦ subset_rfl) x = x :=
  ind (fun _ _ ↦ rfl) x

/-- Refinement maps compose: refining along `τ` and then along `σ` is refining along `τ ∘ σ`. -/
@[simp]
theorem refine_refine (τ : κ → ι) (hτ : ∀ k, V k ⊆ U (τ k)) (σ : ν → κ)
    (hσ : ∀ m, W m ⊆ V (σ m)) (x : NonabelianCechH1 IB IG n G U) :
    refine σ hσ (refine τ hτ x) = refine (τ ∘ σ) (fun m ↦ (hσ m).trans (hτ (σ m))) x :=
  ind (fun _ _ ↦ rfl) x

/-- The refinement map does not depend on the chosen refinement map of index sets. -/
theorem refine_eq_refine (τ τ' : κ → ι) (hτ : ∀ k, V k ⊆ U (τ k))
    (hτ' : ∀ k, V k ⊆ U (τ' k)) :
    refine τ hτ = (refine τ' hτ' : NonabelianCechH1 IB IG n G U → _) :=
  funext <| ind fun _ hc ↦ mk_eq_mk_iff.2 (hc.isContMDiffCohomologous_comp τ τ' hτ hτ')

end NonabelianCechH1

end TauCeti
