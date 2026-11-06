/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.GroupCocycle
public import TauCeti.Geometry.Manifold.FiberBundle.Principal.Equivariant

/-!
# Nonabelian Čech `H¹` of a cover and the classification of principal bundles

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

For an open cover with a chosen chart at each point, this set classifies the principal bundles
glued from cocycles:

* `TauCeti.NonabelianCechH1.mk_eq_mk_iff_exists_equivariant`: the principal bundles glued from two
  `C^n` cocycles are isomorphic, by a `G`-equivariant isomorphism over `B` which is `C^n` for the
  charts through the fibre, exactly when the cocycles have the same class. In chart `i`, a bundle
  map is left multiplication by a `C^n` function `k i`, and the cocycles satisfy
  `c' i j = k j * c i j * (k i)⁻¹` (`TauCeti.IsContMDiffCohomologous.of_equivariant`); conversely
  cohomologous cocycles glue to isomorphic bundles by `TauCeti.diffeomorphOfCohomologous`.
* `TauCeti.NonabelianCechH1.mk_eq_one_iff_exists_section`: a cocycle has trivial class exactly when
  its glued bundle has a global `C^n` section, that is, when the glued bundle is trivial.

Every principal bundle arises in this way. For a family `e i` of trivializations of the atlas of a
`C^n` principal bundle `P` with base sets `U i`, the transition functions
`(e i).coordChange (e j) b 1` form a `C^n` cocycle on `U`
(`TauCeti.isContMDiffGroupCocycle_coordChange`), and when the `U i` cover `B` the bundle glued from
it is equivariantly and `C^n`-isomorphic to `P`
(`TauCeti.exists_equivariant_fiberBundleCoreOfGroupCocycle_coordChange`). Hence two principal
bundles trivialized over the same open cover are isomorphic exactly when their transition cocycles
have the same class in the nonabelian Čech `H¹` of the cover
(`TauCeti.NonabelianCechH1.mk_coordChange_eq_mk_coordChange_iff_exists_equivariant`).

## Main definitions

* `TauCeti.IsContMDiffGroupCocycle`: `C^n` group-valued cocycles on a cover.
* `TauCeti.IsContMDiffCohomologous`: cocycles differing by a `C^n` `0`-cochain.
* `TauCeti.NonabelianCechH1`: the nonabelian Čech `H¹` of a cover, with
  `TauCeti.NonabelianCechH1.refine` its refinement maps.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer, 1993,
  §10.2 and Corollary 10.8 (principal bundles are described by cocycles, and isomorphic bundles by
  cohomologous cocycles).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §2–§3 (coordinate
  bundles, equivalence of coordinate bundles, and the construction from coordinate transformations).
* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer, 1966, §3.1 (the nonabelian
  first Čech cohomology set of a covering and its refinement maps).
-/

public section

open Bundle Filter MulOpposite Set
open TauCeti.ManifoldTotalSpace
open scoped Manifold Topology ContDiff

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

namespace IsContMDiffGroupCocycle

variable {U : ι → Set B} {c : ι → ι → B → G}

/-- The constant cocycle `1`. -/
theorem one : IsContMDiffGroupCocycle IB IG n U fun _ _ _ ↦ (1 : G) :=
  ⟨fun _ _ _ _ _ ↦ mul_one 1, fun _ _ ↦ contMDiffOn_const⟩

/-- The `C^n` cocycle `c` is continuous on the overlaps. -/
theorem continuousOn (hc : IsContMDiffGroupCocycle IB IG n U c) (i j : ι) :
    ContinuousOn (c i j) (U i ∩ U j) :=
  (hc.contMDiffOn i j).continuousOn

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
  rw [← groupCocycle_symm _ _ hc.mul_eq _ _ ⟨hl', hl⟩, mul_assoc,
    hc.mul_eq _ _ _ b ⟨⟨hk', hk⟩, hl⟩, hc.mul_eq _ _ _ b ⟨⟨hk', hl⟩, hl'⟩]

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

/-! ### Classification of glued principal bundles -/

section Glued

/-! The fibres of the bundle glued from a `G`-valued cocycle are type synonyms of `G`, with `G`
acting on the right by right multiplication. Maps between the fibres of two glued bundles are
therefore stated as families `B → G → G`, and `G`-equivariance reads `φ b (p * g) = φ b p * g`. -/

-- `ContinuousMul G` follows from `LieGroup IG n G`; it is assumed to state the glued bundles.
variable [LieGroup IG n G] [ContinuousMul G] {U : ι → Set B} (hU : ∀ i, IsOpen (U i))
  (indexAt : B → ι) (hindex : ∀ b, b ∈ U (indexAt b)) {c c' : ι → ι → B → G}
  (hc : IsContMDiffGroupCocycle IB IG n U c) (hc' : IsContMDiffGroupCocycle IB IG n U c')

/-- **Bundle maps change cocycles by coboundaries.** A fibrewise `G`-equivariant map between the
principal bundles glued from the `C^n` cocycles `c` and `c'` on the same cover, which is `C^n` for
the charts through the fibre, exhibits `c` and `c'` as `C^n`-cohomologous. -/
theorem IsContMDiffCohomologous.of_equivariant (φ : B → G → G)
    (hφ : ∀ b p g, φ b (p * g) = φ b p * g)
    (hφs : ContMDiff (IB.prod IG) (IB.prod IG) n
      (fiberwiseMap (F := G)
        (E := (fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex
          hc.continuousOn).Fiber)
        (E' := (fiberBundleCoreOfGroupCocycle U c' hc'.mul_eq G hU indexAt hindex
          hc'.continuousOn).Fiber) φ)) :
    IsContMDiffCohomologous IB IG n U c c' := by
  let Z := fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex hc.continuousOn
  let Z' := fiberBundleCoreOfGroupCocycle U c' hc'.mul_eq G hU indexAt hindex hc'.continuousOn
  have := contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle n IB IG G U c hc.mul_eq hU indexAt
    hindex hc.continuousOn hc.contMDiffOn
  have := contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle n IB IG G U c' hc'.mul_eq hU indexAt
    hindex hc'.continuousOn hc'.contMDiffOn
  -- An equivariant map of fibres is left multiplication by the image of `1`.
  have hφ1 (b : B) (v : G) : φ b v = φ b 1 * v := by
    simpa using hφ b 1 v
  -- The fibre coordinate in chart `i` of the image of the point with chart-`i` coordinate `1`.
  set k : ι → B → G := fun i b ↦ (Z'.localTriv i ((homeomorph G Z'.Fiber).symm
    (fiberwiseMap (E := Z.Fiber) (E' := Z'.Fiber) φ
      (homeomorph G Z.Fiber ((Z.localTriv i).toOpenPartialHomeomorph.symm (b, 1)))))).2
    with hk_def
  have hk (i : ι) : ContMDiffOn IB IG n (k i) (U i) := by
    have : MemTrivializationAtlas (Z.localTriv i) := ⟨mem_range_self i⟩
    have : MemTrivializationAtlas (Z'.localTriv i) := ⟨mem_range_self i⟩
    have h₁ : ContMDiffOn IB (IB.prod IG) n
        (fun b ↦ homeomorph G Z.Fiber ((Z.localTriv i).toOpenPartialHomeomorph.symm (b, 1)))
        (U i) :=
      (contMDiffOn_trivialization_symm (Z.localTriv i)).comp
        (contMDiff_id.prodMk contMDiff_const).contMDiffOn fun b hb ↦
          (Z.localTriv i).mem_target.2 (by simpa [Z] using hb)
    have h₂ := (contMDiffOn_trivialization (Z'.localTriv i)).comp (hφs.comp_contMDiffOn h₁)
      fun b hb ↦ by
        simpa [Z, Z', fiberwiseMap_homeomorph (E := Z.Fiber) (E' := Z'.Fiber) φ] using hb
    simp only [Function.comp_def] at h₂
    exact contMDiff_snd.comp_contMDiffOn h₂
  have hk_eq (i : ι) (b : B) : k i b = c' (indexAt b) i b * φ b 1 * c i (indexAt b) b := by
    simp only [hk_def, FiberBundleCore.localTriv_symm_apply, Homeomorph.symm_apply_apply,
      fiberwiseMap_homeomorph (E := Z.Fiber) (E' := Z'.Fiber) φ, FiberBundleCore.localTriv_apply,
      Z, Z', fiberBundleCoreOfGroupCocycle_coordChange, fiberBundleCoreOfGroupCocycle_indexAt]
    rw [hφ1 b]
    simp [smul_eq_mul, mul_assoc]
  refine ⟨fun i b ↦ (k i b)⁻¹, fun i ↦ (hk i).inv, fun i j b hb ↦ ?_⟩
  have h1 : c i (indexAt b) b = c j (indexAt b) b * c i j b :=
    (hc.mul_eq _ _ _ b ⟨hb, hindex b⟩).symm
  have h2 : c' i j b = c' (indexAt b) j b * (c' (indexAt b) i b)⁻¹ := by
    rw [← groupCocycle_symm _ _ hc'.mul_eq _ _ ⟨hindex b, hb.1⟩,
      hc'.mul_eq _ _ _ b ⟨⟨hb.1, hindex b⟩, hb.2⟩]
  simp only [inv_inv, hk_eq, h1, h2]
  group

/-- **Cohomologous cocycles glue to isomorphic principal bundles.** If the `C^n` cocycles `c` and
`c'` are `C^n`-cohomologous through `h`, the fibrewise left multiplications by
`(h (indexAt b) b)⁻¹` form a `G`-equivariant isomorphism of the glued principal bundles which is
`C^n` for the charts through the fibre. -/
theorem IsContMDiffCohomologous.exists_equivariant (h : IsContMDiffCohomologous IB IG n U c c') :
    ∃ e : B → G ≃ G, (∀ b p g, e b (p * g) = e b p * g) ∧
      ContMDiff (IB.prod IG) (IB.prod IG) n
        (fiberwiseMap (F := G)
          (E := (fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex
            hc.continuousOn).Fiber)
          (E' := (fiberBundleCoreOfGroupCocycle U c' hc'.mul_eq G hU indexAt hindex
            hc'.continuousOn).Fiber) fun b ↦ e b) := by
  let Z := fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex hc.continuousOn
  let Z' := fiberBundleCoreOfGroupCocycle U c' hc'.mul_eq G hU indexAt hindex hc'.continuousOn
  obtain ⟨h, hh, hcc'⟩ := h
  refine ⟨fun b ↦ Equiv.mulLeft (h (indexAt b) b)⁻¹, fun b p g ↦ (mul_assoc _ p g).symm, ?_⟩
  -- The fibrewise left multiplications are the diffeomorphism glued from `h`.
  refine (diffeomorphOfCohomologous IG c' hc'.mul_eq hc'.continuousOn h hh hcc').contMDiff.congr
    fun x ↦ ?_
  obtain ⟨⟨b, v⟩, rfl⟩ := (homeomorph G Z.Fiber).surjective x
  simp only [Equiv.coe_mulLeft]
  rw [fiberwiseMap_homeomorph (E := Z.Fiber) (E' := Z'.Fiber)
    fun b (v : G) ↦ (h (indexAt b) b)⁻¹ * v]
  -- The glued diffeomorphism acts by `(h (indexAt b) b)⁻¹ • v`, which is left multiplication.
  exact (diffeomorphOfCohomologous_apply (F := G) c' hc'.mul_eq hc'.continuousOn h hh hcc' b v).symm

/-- **Nonabelian Čech `H¹` classifies the glued principal bundles.** The principal bundles glued
from two `C^n` cocycles on the same cover are isomorphic, by a `G`-equivariant isomorphism over
the base which is `C^n` for the charts through the fibre, exactly when the cocycles have the same
class in the nonabelian Čech `H¹`. Such an isomorphism is a diffeomorphism of total spaces by
`TauCeti.PrincipalBundle.diffeomorphOfEquivariant`. -/
theorem NonabelianCechH1.mk_eq_mk_iff_exists_equivariant :
    mk c hc = mk c' hc' ↔
      ∃ e : B → G ≃ G, (∀ b p g, e b (p * g) = e b p * g) ∧
        ContMDiff (IB.prod IG) (IB.prod IG) n
          (fiberwiseMap (F := G)
            (E := (fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex
              hc.continuousOn).Fiber)
            (E' := (fiberBundleCoreOfGroupCocycle U c' hc'.mul_eq G hU indexAt hindex
              hc'.continuousOn).Fiber) fun b ↦ e b) :=
  ⟨fun h ↦ (mk_eq_mk_iff.1 h).exists_equivariant hU indexAt hindex hc hc', fun ⟨e, he, hes⟩ ↦
    mk_eq_mk_iff.2 (.of_equivariant hU indexAt hindex hc hc' (fun b ↦ e b) he hes)⟩

/-- **A cocycle has trivial class exactly when its glued bundle has a smooth section.** The class
of a `C^n` cocycle `c` in the nonabelian Čech `H¹` is the base point exactly when the principal
bundle glued from `c` has a global section `b ↦ ⟨b, s b⟩` which is `C^n` for the charts through
the fibre. -/
theorem NonabelianCechH1.mk_eq_one_iff_exists_section :
    mk c hc = 1 ↔ ∃ s : B → G, ContMDiff IB (IB.prod IG) n fun b ↦
      homeomorph G (fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex
        hc.continuousOn).Fiber ⟨b, s b⟩ := by
  let Z := fiberBundleCoreOfGroupCocycle U c hc.mul_eq G hU indexAt hindex hc.continuousOn
  rw [mk_eq_one_iff]
  constructor
  · rintro ⟨h, hh, hch⟩
    refine ⟨fun b ↦ (h (indexAt b) b)⁻¹, fun b₀ ↦ ?_⟩
    refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨contMDiffAt_id, ?_⟩
    -- Near `b₀`, the section has coordinate `(h (indexAt b₀) b)⁻¹` in the chart at `b₀`.
    refine ((hh (indexAt b₀)).contMDiffAt ((hU _).mem_nhds (hindex b₀))).inv.congr_of_eventuallyEq
      ?_
    -- The trivialization of a glued bundle at a base point is the chart chosen there.
    have htriv : trivializationAt G Z.Fiber b₀ = Z.localTriv (indexAt b₀) :=
      congrArg Z.localTriv (congrFun (fiberBundleCoreOfGroupCocycle_indexAt U c hc.mul_eq G hU
        indexAt hindex hc.continuousOn) b₀)
    filter_upwards [(hU _).mem_nhds (hindex b₀)] with b hb
    simp [htriv, Z, hch _ _ b ⟨hindex b, hb⟩]
  · rintro ⟨s, hs⟩
    have := contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle n IB IG G U c hc.mul_eq hU indexAt
      hindex hc.continuousOn hc.contMDiffOn
    -- The fibre coordinate of the section in chart `i`.
    set k : ι → B → G := fun i b ↦ (Z.localTriv i ⟨b, s b⟩).2 with hk_def
    have hk (i : ι) : ContMDiffOn IB IG n (k i) (U i) := by
      have : MemTrivializationAtlas (Z.localTriv i) := ⟨mem_range_self i⟩
      have h₁ := (contMDiffOn_trivialization (Z.localTriv i)).comp hs.contMDiffOn
        fun b hb ↦ by simpa [Z] using hb
      simp only [Function.comp_def, Z, Homeomorph.symm_apply_apply] at h₁
      exact contMDiff_snd.comp_contMDiffOn h₁
    refine ⟨fun i b ↦ (k i b)⁻¹, fun i ↦ (hk i).inv, fun i j b hb ↦ ?_⟩
    have h1 : c i j b = c (indexAt b) j b * (c (indexAt b) i b)⁻¹ := by
      rw [← groupCocycle_symm _ _ hc.mul_eq _ _ ⟨hindex b, hb.1⟩,
        hc.mul_eq _ _ _ b ⟨⟨hb.1, hindex b⟩, hb.2⟩]
    simp only [hk_def, inv_inv, FiberBundleCore.localTriv_apply, Z,
      fiberBundleCoreOfGroupCocycle_coordChange, fiberBundleCoreOfGroupCocycle_indexAt, smul_eq_mul,
      h1]
    group

end Glued

/-! ### The transition cocycle of a principal bundle -/

section Transition

variable {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [ContMDiffFiberBundle n G P IB IG]
  (e : ι → Trivialization G (π G P)) [∀ i, MemTrivializationAtlas (e i)] {U : ι → Set B}
  (heU : ∀ i, (e i).baseSet = U i)

include heU

variable (IB IG n) in
/-- **The transition functions of a principal bundle form a cocycle.** For a family `e i` of
trivializations of the atlas of a `C^n` principal bundle, the transition functions
`(i, j, b) ↦ (e i).coordChange (e j) b 1` are a `C^n` cocycle on the cover `U` by the base sets
`U i = (e i).baseSet`. By `Bundle.Trivialization.coordChange_eq_mul` they determine all coordinate
changes: `(e i).coordChange (e j) b g = (e i).coordChange (e j) b 1 * g`. -/
theorem isContMDiffGroupCocycle_coordChange :
    IsContMDiffGroupCocycle IB IG n U fun i j b ↦ (e i).coordChange (e j) b 1 where
  mul_eq i j k b hb := by
    simp only [← heU] at hb
    rw [← (e j).coordChange_eq_mul (e k) hb.1.2 hb.2,
      (e i).coordChange_coordChange (e j) (e k) hb.1.1 hb.1.2]
  contMDiffOn i j := (ContMDiffFiberBundle.contMDiffOn_coordChange (e i) (e j)).comp
    (contMDiff_id.prodMk contMDiff_const).contMDiffOn fun _ hb ↦
      ⟨by simpa only [heU, id_eq] using hb, mem_univ _⟩

variable [LieGroup IG n G] [ContinuousMul G] (indexAt : B → ι)
  (hindex : ∀ b, b ∈ U (indexAt b))

/-- **A principal bundle is glued from its transition cocycle.** For a family `e i` of
trivializations of the atlas of a `C^n` principal bundle `P` whose base sets cover `B`, the map
sending the point with fibre coordinate `v` in chart `indexAt b` of the bundle glued from the
transition cocycle to `(e (indexAt b)).symm b v` is a `G`-equivariant isomorphism onto `P`, which
is `C^n` for the charts through the fibre. -/
theorem exists_equivariant_fiberBundleCoreOfGroupCocycle_coordChange :
    ∃ ψ : ∀ b, G ≃ P b, (∀ b v g, ψ b (v * g) = op g • ψ b v) ∧
      ContMDiff (IB.prod IG) (IB.prod IG) n
        (fiberwiseMap (F := G)
          (E := (fiberBundleCoreOfGroupCocycle U (fun i j b ↦ (e i).coordChange (e j) b 1)
            (isContMDiffGroupCocycle_coordChange IB IG n e heU).mul_eq G
            (fun i ↦ heU i ▸ (e i).open_baseSet) indexAt hindex
            (isContMDiffGroupCocycle_coordChange IB IG n e heU).continuousOn).Fiber)
          (E' := P) fun b ↦ ψ b) := by
  have hcoc := isContMDiffGroupCocycle_coordChange IB IG n e heU
  have hU (i : ι) : IsOpen (U i) := heU i ▸ (e i).open_baseSet
  have hindex' (b : B) : b ∈ (e (indexAt b)).baseSet := (heU _).symm ▸ hindex b
  let Z := fiberBundleCoreOfGroupCocycle U (fun i j b ↦ (e i).coordChange (e j) b 1) hcoc.mul_eq G
    hU indexAt hindex hcoc.continuousOn
  have := contMDiffFiberBundle_fiberBundleCoreOfGroupCocycle n IB IG G _ _ hcoc.mul_eq hU indexAt
    hindex hcoc.continuousOn hcoc.contMDiffOn
  have (b : B) : Nonempty (P b) := ⟨(FiberBundle.homeomorphAt G P b).symm 1⟩
  -- The fibre equivalence given by the chart chosen at each base point.
  let ψ : ∀ b, G ≃ P b := fun b ↦
    { toFun := (e (indexAt b)).symm b
      invFun := fun p ↦ (e (indexAt b) ⟨b, p⟩).2
      left_inv := fun v ↦ by simp [(e (indexAt b)).apply_mk_symm (hindex' b)]
      right_inv := fun p ↦ (e (indexAt b)).symm_apply_apply_mk (hindex' b) p }
  have hψ (b : B) (v g : G) : ψ b (v * g) = op g • ψ b v := by
    have hb := hindex' b
    calc (e (indexAt b)).symm b (v * g)
        = (e (indexAt b)).symm b (e (indexAt b) ⟨b, op g • (e (indexAt b)).symm b v⟩).2 := by
          rw [(e (indexAt b)).snd_apply_smul hb, (e (indexAt b)).apply_mk_symm hb]
      _ = op g • (e (indexAt b)).symm b v := (e (indexAt b)).symm_apply_apply_mk hb _
  refine ⟨ψ, hψ, fun x ↦ ?_⟩
  obtain ⟨⟨b₀, v₀⟩, rfl⟩ := (homeomorph G Z.Fiber).surjective x
  set β := indexAt b₀
  have : MemTrivializationAtlas (Z.localTriv β) := ⟨mem_range_self β⟩
  -- Near `b₀`, the map reads `(e β)⁻¹ ∘ (chart β of the glued bundle)`.
  have hsmooth : ContMDiffOn (IB.prod IG) (IB.prod IG) n
      (fun y ↦ homeomorph G P ((e β).toOpenPartialHomeomorph.symm
        (Z.localTriv β ((homeomorph G Z.Fiber).symm y))))
      ((homeomorph G Z.Fiber).symm ⁻¹' (Z.localTriv β).source) :=
    (contMDiffOn_trivialization_symm (e β)).comp (contMDiffOn_trivialization (Z.localTriv β))
      fun y hy ↦ (e β).mem_target.2 (by simpa [Z, heU] using hy)
  have hopen : IsOpen ((homeomorph G Z.Fiber).symm ⁻¹' (Z.localTriv β).source) :=
    (Z.localTriv β).open_source.preimage (homeomorph G Z.Fiber).symm.continuous
  refine (hsmooth.contMDiffAt (hopen.mem_nhds (by simpa [Z] using hindex b₀))).congr_of_eventuallyEq
    (eventually_of_mem (hopen.mem_nhds (by simpa [Z] using hindex b₀)) fun y hy ↦ ?_)
  -- The fibres of the glued bundle are `G`.
  obtain ⟨⟨b, (v : G)⟩, rfl⟩ := (homeomorph G Z.Fiber).surjective y
  simp only [mem_preimage, Homeomorph.symm_apply_apply, FiberBundleCore.mem_localTriv_source, Z,
    fiberBundleCoreOfGroupCocycle_localTriv_baseSet, ← heU] at hy
  have hα := hindex' b
  rw [fiberwiseMap_homeomorph (E := Z.Fiber) (E' := P) fun b ↦ ψ b]
  simp only [Homeomorph.symm_apply_apply, FiberBundleCore.localTriv_apply, Z,
    fiberBundleCoreOfGroupCocycle_coordChange, fiberBundleCoreOfGroupCocycle_indexAt, smul_eq_mul]
  -- The glued chart `β` reads `(e α).coordChange (e β) b v`, which `(e β)⁻¹` sends to `(e α)⁻¹ v`.
  rw [← (e (indexAt b)).coordChange_eq_mul (e β) hα hy, (e (indexAt b)).mk_coordChange (e β) hα hy,
    (e β).symm_apply_apply ((e β).mem_source.2 (by rwa [(e (indexAt b)).proj_symm_apply' hα])),
    ← (e (indexAt b)).mk_symm hα]
  rfl

variable {Q : B → Type*} [TopologicalSpace (TotalSpace G Q)] [∀ b, TopologicalSpace (Q b)]
  [FiberBundle G Q] [∀ b, MulAction Gᵐᵒᵖ (Q b)] [PrincipalBundle G Q]
  [ContMDiffFiberBundle n G Q IB IG] (e' : ι → Trivialization G (π G Q))
  [∀ i, MemTrivializationAtlas (e' i)] (he'U : ∀ i, (e' i).baseSet = U i)

omit indexAt hindex in
/-- **Nonabelian Čech `H¹` classifies principal bundles trivialized over a cover.** Let `P` and `Q`
be `C^n` principal `G`-bundles with families `e i` and `e' i` of trivializations of their atlases
over the same open cover `U` of `B`. Then `P` and `Q` are isomorphic, by a `G`-equivariant
isomorphism over `B` which is `C^n` for the charts through the fibre, exactly when their transition
cocycles have the same class in the nonabelian Čech `H¹` of `U`. -/
theorem NonabelianCechH1.mk_coordChange_eq_mk_coordChange_iff_exists_equivariant
    (hcov : ∀ b, ∃ i, b ∈ U i) :
    mk (fun i j b ↦ (e i).coordChange (e j) b 1)
        (isContMDiffGroupCocycle_coordChange IB IG n e heU) =
      mk (fun i j b ↦ (e' i).coordChange (e' j) b 1)
        (isContMDiffGroupCocycle_coordChange IB IG n e' he'U) ↔
      ∃ φ : ∀ b, P b ≃ Q b, (∀ b (g : G) p, φ b (op g • p) = op g • φ b p) ∧
        ContMDiff (IB.prod IG) (IB.prod IG) n (fiberwiseMap (F := G) fun b ↦ φ b) := by
  choose indexAt hindex using hcov
  have hU (i : ι) : IsOpen (U i) := heU i ▸ (e i).open_baseSet
  have hcoc := isContMDiffGroupCocycle_coordChange IB IG n e heU
  have hcoc' := isContMDiffGroupCocycle_coordChange IB IG n e' he'U
  let Z := fiberBundleCoreOfGroupCocycle U _ hcoc.mul_eq G hU indexAt hindex hcoc.continuousOn
  let Z' := fiberBundleCoreOfGroupCocycle U _ hcoc'.mul_eq G hU indexAt hindex hcoc'.continuousOn
  -- Both bundles are glued from their transition cocycles.
  obtain ⟨ψ, hψ, hψs⟩ :=
    exists_equivariant_fiberBundleCoreOfGroupCocycle_coordChange (IB := IB) (IG := IG) (n := n) e
      heU indexAt hindex
  obtain ⟨ψ', hψ', hψ's⟩ :=
    exists_equivariant_fiberBundleCoreOfGroupCocycle_coordChange (IB := IB) (IG := IG) (n := n) e'
      he'U indexAt hindex
  have hψinv : ContMDiff (IB.prod IG) (IB.prod IG) n
      (fiberwiseMap (F := G) (E := P) (E' := Z.Fiber) fun b ↦ (ψ b).symm) :=
    PrincipalBundle.contMDiff_symm_of_equivariant (P := Z.Fiber) (fun b ↦ ψ b)
      (fun b g p ↦ hψ b p g) hψs
  have hψ'inv : ContMDiff (IB.prod IG) (IB.prod IG) n
      (fiberwiseMap (F := G) (E := Q) (E' := Z'.Fiber) fun b ↦ (ψ' b).symm) :=
    PrincipalBundle.contMDiff_symm_of_equivariant (P := Z'.Fiber) (fun b ↦ ψ' b)
      (fun b g p ↦ hψ' b p g) hψ's
  -- The inverses of `ψ` and `ψ'` are equivariant too.
  have hψsymm (b : B) (g : G) (p : P b) : (ψ b).symm (op g • p) = (ψ b).symm p * g := by
    rw [Equiv.symm_apply_eq, hψ, Equiv.apply_symm_apply]
  have hψ'symm (b : B) (g : G) (q : Q b) : (ψ' b).symm (op g • q) = (ψ' b).symm q * g := by
    rw [Equiv.symm_apply_eq, hψ', Equiv.apply_symm_apply]
  rw [mk_eq_mk_iff_exists_equivariant hU indexAt hindex]
  constructor
  · rintro ⟨χ, hχ, hχs⟩
    refine ⟨fun b ↦ (ψ b).symm.trans ((χ b).trans (ψ' b)), fun b g p ↦ ?_, ?_⟩
    · simp [hψsymm, hχ, hψ']
    · refine (hψ's.comp (hχs.comp hψinv)).congr fun x ↦ ?_
      obtain ⟨p, rfl⟩ := (homeomorph G P).surjective x
      simp only [Function.comp_apply, Equiv.coe_trans,
        fiberwiseMap_homeomorph (E := P) (E' := Q),
        fiberwiseMap_homeomorph (E := P) (E' := Z.Fiber) fun b ↦ (ψ b).symm,
        fiberwiseMap_homeomorph (E := Z.Fiber) (E' := Z'.Fiber) fun b ↦ χ b,
        fiberwiseMap_homeomorph (E := Z'.Fiber) (E' := Q) fun b ↦ ψ' b]
  · rintro ⟨φ, hφ, hφs⟩
    refine ⟨fun b ↦ (ψ b).trans ((φ b).trans (ψ' b).symm), fun b p g ↦ ?_, ?_⟩
    · simp [hψ, hφ, hψ'symm]
    · refine (hψ'inv.comp (hφs.comp hψs)).congr fun x ↦ ?_
      obtain ⟨p, rfl⟩ := (homeomorph G Z.Fiber).surjective x
      rw [fiberwiseMap_homeomorph (E := Z.Fiber) (E' := Z'.Fiber)
        fun b ↦ (ψ b).trans ((φ b).trans (ψ' b).symm)]
      simp only [Function.comp_apply, Equiv.coe_trans,
        fiberwiseMap_homeomorph (E := Z.Fiber) (E' := P) fun b ↦ ψ b,
        fiberwiseMap_homeomorph (E := P) (E' := Q) fun b ↦ φ b,
        fiberwiseMap_homeomorph (E := Q) (E' := Z'.Fiber) fun b ↦ (ψ' b).symm]
      -- The two sides are the same composite, applied to the fibre coordinate.
      rfl

end Transition

end TauCeti
