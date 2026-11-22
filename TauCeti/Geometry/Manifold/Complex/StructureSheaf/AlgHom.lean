/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MaximalIdeal
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Separated
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.RingTheory.LocalRing.AlgHom

/-!
# Complex-algebra homomorphisms of holomorphic stalks and analytic map germs

Constant holomorphic sections give each stalk `(holomorphicStructureSheaf I X).presheaf.stalk x` a
canonical `ℂ`-algebra structure (`instAlgebraStalk` in `StructureSheaf.Basic`), for which
evaluation at `x`, comparison with filter germs, and pullback along analytic maps are `ℂ`-algebra
homomorphisms (`evalAlgHom`, `stalkPrecompAlgHom` in `StructureSheaf.Basic`; `toFilterGermAlgHom`
in `StructureSheaf.Germ`; `stalkPullbackAlgHom` and `stalkPullbackAt` in
`StructureSheaf.StalkPullback`). Because each stalk is a local ring admitting the `ℂ`-algebra
augmentation `evalAlgHom I X x`, every `ℂ`-algebra homomorphism
`ψ : 𝒪_{Y, y} →ₐ[ℂ] 𝒪_{X, x}` between holomorphic stalks automatically reflects units
(`isLocalHom_stalk_algHom`) and commutes with evaluation (`evalAlgHom_comp`, `eval_algHom_apply`),
all established in `StructureSheaf.LocalRing` with no manifold regularity assumption on either
space.

When the target `Y` is a finite-dimensional boundaryless complex manifold and the source stalk
`𝒪_{X, x}` is separated (`IsHausdorff`) with respect to its maximal ideal — in particular whenever
`X` is a boundaryless complex analytic manifold in any dimension
(`instIsHausdorffMaximalIdealStalkOfOmega`) or any finite-dimensional boundaryless complex manifold
(`instIsHausdorffMaximalIdealStalk`) — every `ℂ`-algebra homomorphism `ψ : 𝒪_{Y, y} →ₐ[ℂ] 𝒪_{X, x}`
is induced by pullback along a locally analytic map `(X, x) → (Y, y)` unique up to `=ᶠ[𝓝 x]`:

* When `Y` is modelled on `𝓘(ℂ, E')` with a holomorphic chart `e ∈ maximalAtlas 𝓘(ℂ, E') ω Y` at
  `y`, `OpenPartialHomeomorph.exists_stalkPullbackAt_eq` proves the existence of a map `f : X → Y`
  analytic near `x` sending `x` to `y` such that `stalkPullbackAt hf hfx = ψ`.
* `TauCeti.holomorphicStructureSheaf.analyticMapGermEquivStalkAlgHom` packages the resulting
  bijection between germs along `𝓝 x` of analytic maps `(X, x) → (Y, y)` and `ℂ`-algebra
  homomorphisms `𝒪_{Y, y} →ₐ[ℂ] 𝒪_{X, x}` for any finite-dimensional boundaryless target model `J`,
  independently of charts and bases, and compatibly with identity and composition.

## References

* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Grundlehren der mathematischen
  Wissenschaften 265, Springer, 1984, Chapter 1, §1.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open CategoryTheory Filter IsManifold Opposite TopologicalSpace Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners ℂ E' H'} {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y]

/-! ### Analytic map germs -/

/-- The type of germs along `𝓝 x` of maps `X → Y` that are analytic near `x` and send `x` to `y`. -/
abbrev AnalyticMapGerm (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ E' H')
    (x : X) (y : Y) : Type :=
  {F : Germ (𝓝 x) Y //
    ∃ f : X → Y, (f : Germ (𝓝 x) Y) = F ∧ f x = y ∧ ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w}

/-- Construct an `AnalyticMapGerm` from a map `f : X → Y` analytic near `x` with `f x = y`. -/
def AnalyticMapGerm.mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) : AnalyticMapGerm I J x y :=
  ⟨(f : Germ (𝓝 x) Y), ⟨f, rfl, hfx, hf⟩⟩

/-- The underlying `Germ (𝓝 x) Y` of `AnalyticMapGerm.mk f hf hfx` is `(f : Germ (𝓝 x) Y)`. -/
@[simp]
theorem AnalyticMapGerm.val_mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (AnalyticMapGerm.mk f hf hfx).val = (f : Germ (𝓝 x) Y) := (rfl)

/-- Two `AnalyticMapGerm.mk` germs are equal if and only if their representatives agree near `x`. -/
@[simp]
theorem AnalyticMapGerm.mk_eq_mk {x : X} {y : Y} {f₁ f₂ : X → Y}
    (hf₁ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₁ w) (hfx₁ : f₁ x = y)
    (hf₂ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₂ w) (hfx₂ : f₂ x = y) :
    AnalyticMapGerm.mk f₁ hf₁ hfx₁ = AnalyticMapGerm.mk f₂ hf₂ hfx₂ ↔ f₁ =ᶠ[𝓝 x] f₂ := by
  rw [Subtype.ext_iff, AnalyticMapGerm.val_mk, AnalyticMapGerm.val_mk, Germ.coe_eq]

/-- Every `AnalyticMapGerm` is represented by `AnalyticMapGerm.mk` of a locally analytic map. -/
theorem AnalyticMapGerm.exists_mk {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    ∃ (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y),
      AnalyticMapGerm.mk f hf hfx = F :=
  let ⟨f, hF, hfx, hf⟩ := F.property; ⟨f, hf, hfx, Subtype.ext hF⟩

/-- Every analytic map germ `(X, x) → (Y, y)` tends to `𝓝 y` along `𝓝 x`. -/
theorem AnalyticMapGerm.tendsto {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    F.val.Tendsto (𝓝 y) := by
  obtain ⟨f, hF, hfx, hf⟩ := F.property
  exact hF ▸ Germ.coe_tendsto.2 (hfx ▸ hf.self_of_nhds.continuousAt.tendsto)

/-- The identity analytic map germ at `x`. -/
def AnalyticMapGerm.id (I : ModelWithCorners ℂ E H) (x : X) : AnalyticMapGerm I I x x :=
  AnalyticMapGerm.mk _root_.id (Eventually.of_forall fun _ ↦ contMDiffAt_id) rfl

/-- The underlying `Germ (𝓝 x) X` of `AnalyticMapGerm.id I x` is the germ of `id`. -/
@[simp]
theorem AnalyticMapGerm.val_id (I : ModelWithCorners ℂ E H) (x : X) :
    (AnalyticMapGerm.id I x).val = ((_root_.id : X → X) : Germ (𝓝 x) X) := (rfl)

/-- Pullback of holomorphic stalks along an analytic map germ `F : AnalyticMapGerm I J x y`. -/
def stalkPullbackGerm {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    (holomorphicStructureSheaf J Y).presheaf.stalk y →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x :=
  stalkPullbackAt F.property.choose_spec.2.2 F.property.choose_spec.2.1

/-- Pullback along `AnalyticMapGerm.mk f hf hfx` agrees with `stalkPullbackAt hf hfx`. -/
@[simp]
theorem stalkPullbackGerm_mk {x : X} {y : Y} (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    stalkPullbackGerm (AnalyticMapGerm.mk f hf hfx) = stalkPullbackAt hf hfx := by
  let F := AnalyticMapGerm.mk f hf hfx
  exact stalkPullbackAt_congr F.property.choose_spec.2.2 F.property.choose_spec.2.1 hf hfx
    (Germ.coe_eq.1 F.property.choose_spec.1)

/-- The function germ of `stalkPullbackGerm F s` is composition of the function germ of `s` with
`F.val` via `Germ.compTendsto'`. -/
@[simp]
theorem toFilterGerm_stalkPullbackGerm {x : X} {y : Y} (F : AnalyticMapGerm I J x y)
    (s : (holomorphicStructureSheaf J Y).presheaf.stalk y) :
    toFilterGerm I X x (𝓝 x) le_rfl (stalkPullbackGerm F s) =
      (toFilterGerm J Y y (𝓝 y) le_rfl s).compTendsto' F.val F.tendsto := by
  obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk
  rw [stalkPullbackGerm_mk, toFilterGerm_stalkPullbackAt]
  exact Germ.inductionOn (toFilterGerm J Y y (𝓝 y) le_rfl s) fun _ ↦ rfl

/-- Pullback along `AnalyticMapGerm.id` is the identity `ℂ`-algebra homomorphism. -/
@[simp]
theorem stalkPullbackGerm_id (x : X) :
    stalkPullbackGerm (AnalyticMapGerm.id I x) =
      AlgHom.id ℂ ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  simp [AnalyticMapGerm.id]

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''}
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- Composition of analytic map germs `(X, x) → (Y, y)` and `(Y, y) → (Z, z)`. -/
def AnalyticMapGerm.comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) : AnalyticMapGerm I K x z :=
  ⟨G.val.compTendsto' F.val F.tendsto, by
    obtain ⟨g, hG, hgy, hg⟩ := G.property; obtain ⟨f, hF, hfx, hf⟩ := F.property
    exact ⟨g ∘ f, by simp [← hG, ← hF], (congrArg g hfx).trans hgy,
      eventually_contMDiffAt_comp hg hf hfx⟩⟩

/-- The underlying filter germ of `G.comp F` is `G.val.compTendsto' F.val F.tendsto`. -/
@[simp]
theorem AnalyticMapGerm.val_comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    (G.comp F).val = G.val.compTendsto' F.val F.tendsto := (rfl)

/-- Composing `AnalyticMapGerm.mk` representatives produces `AnalyticMapGerm.mk (g ∘ f) _ _`. -/
@[simp]
theorem AnalyticMapGerm.comp_mk {x : X} {y : Y} {z : Z}
    (g : Y → Z) (hg : ∀ᶠ v in 𝓝 y, ContMDiffAt J K ω g v) (hgy : g y = z)
    (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (AnalyticMapGerm.mk g hg hgy).comp (AnalyticMapGerm.mk f hf hfx) =
      AnalyticMapGerm.mk (g ∘ f) (eventually_contMDiffAt_comp hg hf hfx)
        ((congrArg g hfx).trans hgy) :=
  Subtype.ext rfl

/-- Left composition with `AnalyticMapGerm.id` is the identity. -/
@[simp]
theorem AnalyticMapGerm.id_comp {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    (AnalyticMapGerm.id J y).comp F = F := by obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk; rfl

/-- Right composition with `AnalyticMapGerm.id` is the identity. -/
@[simp]
theorem AnalyticMapGerm.comp_id {x : X} {y : Y} (F : AnalyticMapGerm I J x y) :
    F.comp (AnalyticMapGerm.id I x) = F := by obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk; rfl

/-- Composition of analytic map germs is associative. -/
theorem AnalyticMapGerm.comp_assoc {E''' : Type*} [NormedAddCommGroup E'''] [NormedSpace ℂ E''']
    {H''' : Type*} [TopologicalSpace H'''] {L : ModelWithCorners ℂ E''' H'''}
    {W : Type} [TopologicalSpace W] [ChartedSpace H''' W] {x : X} {y : Y} {z : Z} {w : W}
    (H : AnalyticMapGerm K L z w) (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    (H.comp G).comp F = H.comp (G.comp F) := by
  obtain ⟨h, hh, hhz, rfl⟩ := H.exists_mk; obtain ⟨g, hg, hgy, rfl⟩ := G.exists_mk
  obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk; rfl

-- Pre-order so pullback composition splits before `AnalyticMapGerm.comp_mk` merges `mk` germs.
/-- Stalk pullback is contravariantly functorial under composition of analytic map germs. -/
@[simp↓]
theorem stalkPullbackGerm_comp {x : X} {y : Y} {z : Z}
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    stalkPullbackGerm (G.comp F) = (stalkPullbackGerm F).comp (stalkPullbackGerm G) := by
  obtain ⟨g, hg, hgy, rfl⟩ := G.exists_mk; obtain ⟨f, hf, hfx, rfl⟩ := F.exists_mk
  rw [AnalyticMapGerm.comp_mk (J := J), stalkPullbackGerm_mk, stalkPullbackGerm_mk,
    stalkPullbackGerm_mk, stalkPullbackAt_comp (J := J)]

end Algebra

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
  (e : OpenPartialHomeomorph Y E') (he : e ∈ maximalAtlas 𝓘(ℂ, E') ω Y)

include he in
/-- Two locally analytic maps `(X, x) → (Y, y)` whose stalk pullbacks agree on the centered linear
coordinate germs of a holomorphic chart `e` at `y` along a basis `b` agree on a neighbourhood of
`x`. -/
theorem eventuallyEq_of_stalkPullbackAt_eq_on_coordinates {ι : Type*} (b : Module.Basis ι ℂ E')
    {x : X} {y : Y} (hy : y ∈ e.source) {f₁ f₂ : X → Y}
    (hf₁ : ∀ᶠ w in 𝓝 x, ContMDiffAt I 𝓘(ℂ, E') ω f₁ w) (hfx₁ : f₁ x = y)
    (hf₂ : ∀ᶠ w in 𝓝 x, ContMDiffAt I 𝓘(ℂ, E') ω f₂ w) (hfx₂ : f₂ x = y)
    (hcoord : ∀ i : ι,
      stalkPullbackAt hf₁ hfx₁
        (e.holomorphicLinearCoordinateGerm he y (LinearMap.toContinuousLinearMap (b.coord i)) hy) =
      stalkPullbackAt hf₂ hfx₂
        (e.holomorphicLinearCoordinateGerm he y (LinearMap.toContinuousLinearMap (b.coord i)) hy)) :
    f₁ =ᶠ[𝓝 x] f₂ := by
  have := Module.Finite.finite_basis b
  have hmem₁ : ∀ᶠ w in 𝓝 x, f₁ w ∈ e.source :=
    (hfx₁ ▸ hf₁.self_of_nhds.continuousAt.tendsto).eventually (e.open_source.mem_nhds hy)
  have hmem₂ : ∀ᶠ w in 𝓝 x, f₂ w ∈ e.source :=
    (hfx₂ ▸ hf₂.self_of_nhds.continuousAt.tendsto).eventually (e.open_source.mem_nhds hy)
  have hall : ∀ᶠ w in 𝓝 x, ∀ i : ι, b.coord i (e (f₁ w) - e y) = b.coord i (e (f₂ w) - e y) :=
    eventually_all.2 fun i ↦ by
      have hi := congrArg (toFilterGerm I X x (𝓝 x) le_rfl) (hcoord i)
      rwa [toFilterGerm_stalkPullbackAt, toFilterGerm_stalkPullbackAt,
        e.toFilterGerm_holomorphicLinearCoordinateGerm he y _ hy,
        Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq] at hi
  filter_upwards [hmem₁, hmem₂, hall] with w hw₁ hw₂ hw
  exact e.injOn hw₁ hw₂ (sub_left_inj.1 (b.ext_elem hw))

include he in
/-- Given a holomorphic chart `e ∈ maximalAtlas 𝓘(ℂ, E') ω Y` around `y` and a
maximal-ideal-separated (`IsHausdorff`) source stalk `𝒪_{X, x}`, every `ℂ`-algebra homomorphism
`ψ : 𝒪_{Y, y} →ₐ[ℂ] 𝒪_{X, x}` is `stalkPullbackAt hf hfx` for a map `f : X → Y` analytic near `x`
with `f x = y`. -/
theorem exists_stalkPullbackAt_eq {x : X} {y : Y} (hy : y ∈ e.source)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)]
    (ψ : (holomorphicStructureSheaf 𝓘(ℂ, E') Y).presheaf.stalk y →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x) :
    ∃ (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I 𝓘(ℂ, E') ω f w) (hfx : f x = y),
      stalkPullbackAt hf hfx = ψ := by
  let b := Module.finBasis ℂ E'
  let z : Fin (Module.finrank ℂ E') → (holomorphicStructureSheaf 𝓘(ℂ, E') Y).presheaf.stalk y :=
    fun i ↦
      e.holomorphicLinearCoordinateGerm he y (LinearMap.toContinuousLinearMap (b.coord i)) hy
  choose u hu_cm hu_germ using fun i ↦ exists_toFilterGerm_eq x (ψ (z i))
  have hux (i : Fin (Module.finrank ℂ E')) : u i x = 0 := by
    rw [← eval_eq_of_toFilterGerm_eq (hu_germ i (𝓝 x) le_rfl), eval_algHom_apply]
    exact e.eval_holomorphicLinearCoordinateGerm he y _ hy
  let g : X → E' := fun w ↦ e y + ∑ i, u i w • b i
  have hgx : g x = e y := by simp [g, hux]
  have hg_cm : ∀ᶠ w in 𝓝 x, ContMDiffAt I 𝓘(ℂ, E') ω g w := by
    filter_upwards [eventually_all.2 hu_cm] with w hw
    refine contMDiffAt_const.add (ContMDiffAt.sum fun i _ ↦ ?_)
    exact ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (b i)).contDiff
      (n := ω)).contMDiff.contMDiffAt.comp w (hw i)
  have hg_mem : ∀ᶠ w in 𝓝 x, g w ∈ e.target :=
    (hgx ▸ hg_cm.self_of_nhds.continuousAt.tendsto).eventually
      (e.open_target.mem_nhds (e.map_source hy))
  let f : X → Y := e.symm ∘ g
  have hfx : f x = y := by simp [f, hgx, e.left_inv hy]
  have hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I 𝓘(ℂ, E') ω f w := by
    filter_upwards [hg_cm, hg_mem] with w hgw hgt
    exact ((contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt
      (e.open_target.mem_nhds hgt)).comp w hgw
  refine ⟨f, hf, hfx, AlgHom.ext_of_span_eq_maximalIdeal
    (evalAlgHom 𝓘(ℂ, E') Y y).surjective_algebraMap_residueField
    ((e.ker_eval_eq_span_holomorphicLinearCoordinateGerm he b hy).symm.trans
      (maximalIdeal_stalk 𝓘(ℂ, E') Y y).symm) ?_⟩
  rintro _ ⟨i, rfl⟩
  apply toFilterGerm_nhds_injective x
  rw [toFilterGerm_stalkPullbackAt, hu_germ i (𝓝 x) le_rfl,
    e.toFilterGerm_holomorphicLinearCoordinateGerm he y _ hy, Germ.coe_compTendsto, Germ.coe_eq]
  filter_upwards [hg_mem] with w hwt
  simp [f, g, e.right_inv hwt, map_sum, Finsupp.single_apply]

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

section GermEquivalence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℂ E H} {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℂ E' H'} [J.Boundaryless]
  {Y : Type} [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J 1 Y]

/-- Two locally analytic maps from `(X, x)` into a finite-dimensional boundaryless complex manifold
`(Y, y)` induce the same `ℂ`-algebra homomorphism on holomorphic stalks if and only if they agree
on a neighbourhood of `x`. No manifold assumption on `X` is required. -/
theorem stalkPullbackAt_eq_iff_eventuallyEq {x : X} {y : Y} {f₁ f₂ : X → Y}
    (hf₁ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₁ w) (hfx₁ : f₁ x = y)
    (hf₂ : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f₂ w) (hfx₂ : f₂ x = y) :
    stalkPullbackAt hf₁ hfx₁ = stalkPullbackAt hf₂ hfx₂ ↔ f₁ =ᶠ[𝓝 x] f₂ := by
  refine ⟨fun heq ↦ ?_, stalkPullbackAt_congr hf₁ hfx₁ hf₂ hfx₂⟩
  have : IsManifold J ω Y := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let V : Type := Fin (Module.finrank ℂ E') → ℂ
  let L : E' ≃L[ℂ] V := LinearEquiv.toContinuousLinearEquiv (Module.finBasis ℂ E').equivFun
  have hΦ := eventually_contMDiffAt_comp_extChartAt (I := J) (n := ω) y L.contDiff
  have hcomp :
      stalkPullbackAt (eventually_contMDiffAt_comp hΦ hf₁ hfx₁)
        (congrArg (L ∘ extChartAt J y) hfx₁) =
      stalkPullbackAt (eventually_contMDiffAt_comp hΦ hf₂ hfx₂)
        (congrArg (L ∘ extChartAt J y) hfx₂) := by
    rw [stalkPullbackAt_comp hΦ rfl hf₁ hfx₁, stalkPullbackAt_comp hΦ rfl hf₂ hfx₂, heq]
  have hevV := (OpenPartialHomeomorph.refl V).eventuallyEq_of_stalkPullbackAt_eq_on_coordinates
    (contDiffGroupoid ω 𝓘(ℂ, V)).id_mem_maximalAtlas (Pi.basisFun ℂ (Fin (Module.finrank ℂ E')))
    (Set.mem_univ _) _ _ _ _ fun i ↦ AlgHom.congr_fun hcomp _
  have hmem₁ : ∀ᶠ w in 𝓝 x, f₁ w ∈ (extChartAt J y).source :=
    (hfx₁ ▸ hf₁.self_of_nhds.continuousAt.tendsto).eventually (extChartAt_source_mem_nhds y)
  have hmem₂ : ∀ᶠ w in 𝓝 x, f₂ w ∈ (extChartAt J y).source :=
    (hfx₂ ▸ hf₂.self_of_nhds.continuousAt.tendsto).eventually (extChartAt_source_mem_nhds y)
  filter_upwards [hevV, hmem₁, hmem₂] with w hw hw₁ hw₂
  exact (extChartAt J y).injOn hw₁ hw₂ (L.injective hw)

/-- **Every `ℂ`-algebra homomorphism of holomorphic stalks comes from a locally analytic map.** If
`Y` is a finite-dimensional boundaryless complex manifold and the stalk `𝒪_{X, x}` is separated
(`IsHausdorff`) with respect to its maximal ideal, then every `ℂ`-algebra homomorphism
`ψ : 𝒪_{Y, y} →ₐ[ℂ] 𝒪_{X, x}` is `stalkPullbackAt hf hfx` for a map `f : X → Y` analytic near `x`
with `f x = y`. -/
theorem exists_stalkPullbackAt_eq (x : X) (y : Y)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)]
    (ψ : (holomorphicStructureSheaf J Y).presheaf.stalk y →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x) :
    ∃ (f : X → Y) (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y),
      stalkPullbackAt hf hfx = ψ := by
  have : IsManifold J ω Y := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let V : Type := Fin (Module.finrank ℂ E') → ℂ
  let L : E' ≃L[ℂ] V := LinearEquiv.toContinuousLinearEquiv (Module.finBasis ℂ E').equivFun
  let Φ : Y → V := L ∘ extChartAt J y
  have hΦ := eventually_contMDiffAt_comp_extChartAt (I := J) (n := ω) y L.contDiff
  obtain ⟨g, hg, hgx, hgψ⟩ := (OpenPartialHomeomorph.refl V).exists_stalkPullbackAt_eq
    (contDiffGroupoid ω 𝓘(ℂ, V)).id_mem_maximalAtlas (Set.mem_univ (Φ y))
    (ψ.comp (stalkPullbackAlgHom hΦ))
  let Ψ : V → Y := (extChartAt J y).symm ∘ L.symm
  have hmemV : ∀ᶠ z in 𝓝 (Φ y), L.symm z ∈ (extChartAt J y).target :=
    (by simpa [Φ] using L.symm.continuous.tendsto (Φ y) :
      Tendsto L.symm (𝓝 (Φ y)) (𝓝 (extChartAt J y y))).eventually (extChartAt_target_mem_nhds y)
  have hΨ : ∀ᶠ z in 𝓝 (Φ y), ContMDiffAt 𝓘(ℂ, V) J ω Ψ z :=
    hmemV.mono fun z hz ↦ ((contMDiffOn_extChartAt_symm (n := ω) y).contMDiffAt
      (extChartAt_target_mem_nhds' hz)).comp z L.symm.contDiff.contMDiff.contMDiffAt
  have hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω (Ψ ∘ g) w := eventually_contMDiffAt_comp hΨ hg hgx
  have hfx : (Ψ ∘ g) x = y := (congrArg Ψ hgx).trans (by simp [Ψ, Φ])
  refine ⟨Ψ ∘ g, hf, hfx, ?_⟩
  have hΦf_eq : Φ ∘ (Ψ ∘ g) =ᶠ[𝓝 x] g := by
    filter_upwards [(hgx ▸ hg.self_of_nhds.continuousAt.tendsto).eventually hmemV] with w hw
    simp only [Function.comp_apply, Φ, Ψ, (extChartAt J y).right_inv hw,
      ContinuousLinearEquiv.apply_symm_apply]
  have hcomp : (stalkPullbackAt hf hfx).comp (stalkPullbackAlgHom hΦ) =
      ψ.comp (stalkPullbackAlgHom hΦ) := calc
    (stalkPullbackAt hf hfx).comp (stalkPullbackAlgHom hΦ)
      = (stalkPullbackAt hf hfx).comp (stalkPullbackAt hΦ rfl) := by rw [stalkPullbackAt_rfl]
    _ = stalkPullbackAt hg hgx := by
          rw [← stalkPullbackAt_comp hΦ rfl hf hfx]
          exact stalkPullbackAt_congr _ _ hg hgx hΦf_eq
    _ = ψ.comp (stalkPullbackAlgHom hΦ) := hgψ
  refine (AlgHom.cancel_right ?_).1 hcomp
  intro s
  obtain ⟨t, ht⟩ := (stalkEquivModelSpace y L).symm.surjective s
  refine ⟨t, ?_⟩
  rw [stalkPullbackAlgHom_apply, ← ht, stalkEquivModelSpace_symm_apply]

/-- **Equivalence between analytic map germs and `ℂ`-algebra homomorphisms of holomorphic stalks.**
For any finite-dimensional boundaryless complex manifold `Y` and any complex charted space `X`
whose stalk at `x` is maximal-ideal separated (`IsHausdorff`), germs along `𝓝 x` of maps `X → Y`
analytic near `x` sending `x` to `y` correspond bijectively via `stalkPullbackGerm` to `ℂ`-algebra
homomorphisms `𝒪_{Y, y} →ₐ[ℂ] 𝒪_{X, x}`. -/
def analyticMapGermEquivStalkAlgHom (x : X) (y : Y)
    [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x)] :
    AnalyticMapGerm I J x y ≃
      ((holomorphicStructureSheaf J Y).presheaf.stalk y →ₐ[ℂ]
        (holomorphicStructureSheaf I X).presheaf.stalk x) :=
  Equiv.ofBijective stalkPullbackGerm
    ⟨fun F₁ F₂ h ↦ Subtype.ext <| by
        rw [← F₁.property.choose_spec.1, ← F₂.property.choose_spec.1, Germ.coe_eq]
        exact (stalkPullbackAt_eq_iff_eventuallyEq
          F₁.property.choose_spec.2.2 F₁.property.choose_spec.2.1
          F₂.property.choose_spec.2.2 F₂.property.choose_spec.2.1).1 h,
      fun ψ ↦ by
        obtain ⟨f, hf, hfx, rfl⟩ := exists_stalkPullbackAt_eq x y ψ
        exact ⟨AnalyticMapGerm.mk f hf hfx, stalkPullbackGerm_mk f hf hfx⟩⟩

section EquivSimp

variable {x : X} {y : Y}
  [IsHausdorff (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
    ((holomorphicStructureSheaf I X).presheaf.stalk x)]

-- Pre-order so the forward equivalence routes through `stalkPullbackGerm` before `comp_mk` fires.
/-- In the forward direction, `analyticMapGermEquivStalkAlgHom` is `stalkPullbackGerm`. -/
@[simp↓]
theorem analyticMapGermEquivStalkAlgHom_apply (F : AnalyticMapGerm I J x y) :
    analyticMapGermEquivStalkAlgHom x y F = stalkPullbackGerm F := (rfl)

/-- Pulling back along `(analyticMapGermEquivStalkAlgHom x y).symm ψ` recovers `ψ`. -/
@[simp]
theorem stalkPullbackGerm_analyticMapGermEquivStalkAlgHom_symm
    (ψ : (holomorphicStructureSheaf J Y).presheaf.stalk y →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x) :
    stalkPullbackGerm ((analyticMapGermEquivStalkAlgHom x y).symm ψ) = ψ :=
  (analyticMapGermEquivStalkAlgHom x y).apply_symm_apply ψ

/-- `(analyticMapGermEquivStalkAlgHom x y).symm` of `stalkPullbackGerm F` recovers `F`. -/
@[simp]
theorem analyticMapGermEquivStalkAlgHom_symm_stalkPullbackGerm (F : AnalyticMapGerm I J x y) :
    (analyticMapGermEquivStalkAlgHom x y).symm (stalkPullbackGerm F) = F :=
  (analyticMapGermEquivStalkAlgHom x y).symm_apply_apply F

/-- `analyticMapGermEquivStalkAlgHom` on `AnalyticMapGerm.mk f hf hfx` equals
`stalkPullbackAt hf hfx`. -/
theorem analyticMapGermEquivStalkAlgHom_mk (f : X → Y)
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    analyticMapGermEquivStalkAlgHom x y (AnalyticMapGerm.mk f hf hfx) = stalkPullbackAt hf hfx :=
  stalkPullbackGerm_mk f hf hfx

/-- `(analyticMapGermEquivStalkAlgHom x y).symm` of `stalkPullbackAt hf hfx` recovers
`AnalyticMapGerm.mk f hf hfx`. -/
@[simp]
theorem analyticMapGermEquivStalkAlgHom_symm_stalkPullbackAt {f : X → Y}
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) (hfx : f x = y) :
    (analyticMapGermEquivStalkAlgHom x y).symm (stalkPullbackAt hf hfx) =
      AnalyticMapGerm.mk f hf hfx := by
  rw [← stalkPullbackGerm_mk f hf hfx, analyticMapGermEquivStalkAlgHom_symm_stalkPullbackGerm]

/-- `(analyticMapGermEquivStalkAlgHom x (f x)).symm` of `stalkPullbackAlgHom hf` recovers
`AnalyticMapGerm.mk f hf rfl`. -/
@[simp]
theorem analyticMapGermEquivStalkAlgHom_symm_stalkPullbackAlgHom {f : X → Y}
    (hf : ∀ᶠ w in 𝓝 x, ContMDiffAt I J ω f w) :
    (analyticMapGermEquivStalkAlgHom x (f x)).symm (stalkPullbackAlgHom hf) =
      AnalyticMapGerm.mk f hf rfl := by
  rw [← stalkPullbackAt_rfl, analyticMapGermEquivStalkAlgHom_symm_stalkPullbackAt]

section Comp

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℂ E''] [FiniteDimensional ℂ E'']
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℂ E'' H''} [K.Boundaryless]
  {Z : Type} [TopologicalSpace Z] [ChartedSpace H'' Z] [IsManifold K 1 Z] {z : Z}

/-- `analyticMapGermEquivStalkAlgHom` sends composition of analytic map germs to reverse
composition of `ℂ`-algebra homomorphisms. -/
theorem analyticMapGermEquivStalkAlgHom_comp
    (G : AnalyticMapGerm J K y z) (F : AnalyticMapGerm I J x y) :
    analyticMapGermEquivStalkAlgHom x z (G.comp F) =
      (analyticMapGermEquivStalkAlgHom x y F).comp (analyticMapGermEquivStalkAlgHom y z G) :=
  stalkPullbackGerm_comp G F

/-- `analyticMapGermEquivStalkAlgHom.symm` sends composition of `ℂ`-algebra homomorphisms to
reverse composition of analytic map germs. -/
@[simp]
theorem analyticMapGermEquivStalkAlgHom_symm_comp
    (ψ : (holomorphicStructureSheaf J Y).presheaf.stalk y →ₐ[ℂ]
      (holomorphicStructureSheaf I X).presheaf.stalk x)
    (χ : (holomorphicStructureSheaf K Z).presheaf.stalk z →ₐ[ℂ]
      (holomorphicStructureSheaf J Y).presheaf.stalk y) :
    (analyticMapGermEquivStalkAlgHom (I := I) (J := K) x z).symm (ψ.comp χ) =
      ((analyticMapGermEquivStalkAlgHom (I := J) (J := K) y z).symm χ).comp
        ((analyticMapGermEquivStalkAlgHom (I := I) (J := J) x y).symm ψ) :=
  (analyticMapGermEquivStalkAlgHom (I := I) (J := K) x z).injective (by simp)

end Comp

end EquivSimp

/-- `analyticMapGermEquivStalkAlgHom` sends the identity analytic map germ to `AlgHom.id`. -/
theorem analyticMapGermEquivStalkAlgHom_id [FiniteDimensional ℂ E] [I.Boundaryless]
    [IsManifold I 1 X] (x : X) :
    analyticMapGermEquivStalkAlgHom (I := I) (J := I) x x (AnalyticMapGerm.id I x) =
      AlgHom.id ℂ ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  stalkPullbackGerm_id x

/-- `(analyticMapGermEquivStalkAlgHom x x).symm` sends `AlgHom.id` to `AnalyticMapGerm.id`. -/
@[simp]
theorem analyticMapGermEquivStalkAlgHom_symm_id [FiniteDimensional ℂ E] [I.Boundaryless]
    [IsManifold I 1 X] (x : X) :
    (analyticMapGermEquivStalkAlgHom (I := I) (J := I) x x).symm (AlgHom.id ℂ _) =
      AnalyticMapGerm.id I x :=
  (analyticMapGermEquivStalkAlgHom (I := I) (J := I) x x).symm_apply_eq.2
    (analyticMapGermEquivStalkAlgHom_id x).symm

end GermEquivalence

end TauCeti.holomorphicStructureSheaf
