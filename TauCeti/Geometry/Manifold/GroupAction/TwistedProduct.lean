/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Closed
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.GroupAction.Quotient
public import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse
public import TauCeti.Topology.Covering.BalancedProduct.Basic
import TauCeti.Geometry.Lie.AutomaticSmoothness
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Twisted products `G ×_K B`

Let `K` be a subgroup of a finite-dimensional real Lie group `G` which is a finite-dimensional
Lie group for the subspace topology, such as a compact or, by Cartan's theorem
(`TauCeti.Lie.isEmbeddedLieSubgroup_of_isClosed`), any closed subgroup; it is then closed
(`TauCeti.Lie.isClosed_of_chartedSpace`). Let `K` act smoothly on a boundaryless Hausdorff
manifold `B`, for instance on a `K`-invariant open subset of a representation. The **twisted
product** `G ×_K B` is the orbit space of the action `k • (g, b) = (g * k⁻¹, k • b)` of `K` on
`G × B`. This action is free and proper, so the quotient manifold theorem
(`ProperSMul.instIsManifoldOrbitRelQuotient`) makes `G ×_K B` a smooth manifold of dimension
`dim G + dim B - dim K` for which the projection `(g, b) ↦ [g, b]` is a smooth submersion. The
group `G` acts on it smoothly from the left by `g • [g', b] = [g * g', b]`.

Taking for `B` the one-point space `Unit` gives the orbit space `G ×_K pt` of the right action
of `K` on `G` by multiplication, the space of cosets `gK`; we use this orbit space for `G ⧸ K`.
The projection `[g, b] ↦ [g]` onto it is smooth and `G`-equivariant. When `b₀ : B` is fixed by
`K`, the zero section `[g] ↦ [g, b₀]` is a `G`-equivariant smooth embedding whose image is the
`G`-orbit of `[1, b₀]`: it is a smooth section of the projection.

In the slice theorem, `K` is the compact stabilizer of a point `x` of a proper `G`-manifold and
`B` a small invariant ball in the normal space to the orbit at `x`; the model `G ×_K B` maps
diffeomorphically onto an invariant neighbourhood of the orbit, the zero section going to the
orbit itself.

The twisted product is the balanced product `TauCeti.BalancedProduct K (RightMul G) B`, where `K`
acts on the type synonym `TauCeti.TwistedProduct.RightMul G` of `G` by `k • g = g * k⁻¹`, so that
this action does not clash with the left multiplication of `K` on `G`.

## Main definitions and results

* `TauCeti.TwistedProduct K B`: the twisted product `G ×_K B`, with classes
  `TauCeti.TwistedProduct.mk K g b`; maps out of it are `TauCeti.TwistedProduct.lift f hf` for
  `f : G → B → X` with `f (g * k⁻¹) (k • b) = f g b`.
* `TauCeti.TwistedProduct.instProperSMulProd`, `TauCeti.TwistedProduct.instIsCancelSMulProd`:
  the action of a closed subgroup `K` on `G × B` is proper and free.
* `TauCeti.TwistedProduct.chartedSpace`: the smooth structure of `G ×_K B` from the quotient
  manifold theorem, for which `TauCeti.TwistedProduct.isSubmersion_mk` makes the projection
  from `G × B` a smooth submersion.
* `TauCeti.TwistedProduct.contMDiffSMul`: the left action of `G` on `G ×_K B` is smooth.
* `TauCeti.TwistedProduct.proj`, `TauCeti.TwistedProduct.contMDiff_proj`: the smooth
  equivariant projection `G ×_K B → G ×_K pt`.
* `TauCeti.TwistedProduct.zeroSection`,
  `TauCeti.TwistedProduct.isSmoothEmbedding_zeroSection`,
  `TauCeti.TwistedProduct.range_zeroSection`: for a `K`-fixed point `b₀`, the zero section is a
  smooth embedding onto the orbit of `[1, b₀]`.

## References

* E. Meinrenken, *Group actions on manifolds*, lecture notes, University of Toronto, 2003,
  Section 1.6 and the proof of Theorem 1.25.
* J. J. Duistermaat and J. A. C. Kolk, *Lie Groups*, Springer, 2000, Section 2.4.
-/

public section

noncomputable section

open Function Set Filter Manifold Topology
open scoped ContDiff Manifold

namespace TauCeti

namespace TwistedProduct

/-- The group `G` as a space on which a subgroup `K` acts from the left by right multiplication
with the inverse, `k • g = g * k⁻¹` (`TauCeti.TwistedProduct.RightMul.instMulAction`). It is a
type synonym of `G`, so that this action does not clash with the left multiplication of `K`. -/
def RightMul (G : Type*) : Type _ := G

variable {G B : Type*}

/-- The element `g` of `G` as a point of `TauCeti.TwistedProduct.RightMul G`. -/
def RightMul.mk (g : G) : RightMul G := g

/-- The element of `G` underlying a point of `TauCeti.TwistedProduct.RightMul G`. -/
def RightMul.val (g : RightMul G) : G := g

/-- The element underlying `RightMul.mk g` is `g`. -/
@[simp]
theorem RightMul.val_mk (g : G) : (RightMul.mk g).val = g :=
  (rfl)

/-- A point of `RightMul G` is the `RightMul.mk` of its underlying element. -/
@[simp]
theorem RightMul.mk_val (g : RightMul G) : RightMul.mk g.val = g :=
  (rfl)

/-- Points of `RightMul G` with the same underlying element are equal. -/
theorem RightMul.ext {g g' : RightMul G} (h : g.val = g'.val) : g = g' :=
  h

section Structure

variable [TopologicalSpace G]

/-- The topology of `G`. -/
instance RightMul.instTopologicalSpace : TopologicalSpace (RightMul G) :=
  inferInstanceAs (TopologicalSpace G)

/-- The identification of `RightMul G` with `G` is continuous. -/
theorem RightMul.continuous_val : Continuous (RightMul.val : RightMul G → G) :=
  continuous_id

/-- The identification of `G` with `RightMul G` is continuous. -/
theorem RightMul.continuous_mk : Continuous (RightMul.mk : G → RightMul G) :=
  continuous_id

variable {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG} [ChartedSpace HG G]

/-- The charts of `G`. -/
instance RightMul.instChartedSpace : ChartedSpace HG (RightMul G) :=
  inferInstanceAs (ChartedSpace HG G)

/-- `RightMul G` is the manifold `G`. -/
instance RightMul.instIsManifold {n : ℕ∞ω} [IsManifold IG n G] :
    IsManifold IG n (RightMul G) :=
  inferInstanceAs (IsManifold IG n G)

end Structure

variable [Group G] {K : Subgroup G}

/-- The scalar multiplication `k • g = g * k⁻¹` of `K` on `RightMul G`. -/
instance RightMul.instSMul : SMul K (RightMul G) where
  smul k g := RightMul.mk (g.val * (k : G)⁻¹)

/-- `k • g = g * k⁻¹`. -/
@[simp]
theorem RightMul.val_smul (k : K) (g : RightMul G) : (k • g).val = g.val * (k : G)⁻¹ :=
  (rfl)

/-- The action `k • g = g * k⁻¹` of `K` on `RightMul G`. -/
instance RightMul.instMulAction : MulAction K (RightMul G) where
  one_smul g := RightMul.ext (by simp)
  mul_smul k k' g := RightMul.ext (by simp [mul_assoc])

/-- The action of `K` on `RightMul G` is free. -/
instance RightMul.instIsCancelSMul : IsCancelSMul K (RightMul G) where
  toIsLeftCancelSMul := inferInstance
  right_cancel' k k' g h := by
    have h₁ := congrArg RightMul.val h
    simp only [RightMul.val_smul, mul_right_inj, inv_inj] at h₁
    exact Subtype.ext h₁

/-- The diagonal action of `K` on `RightMul G × B`, `k • (g, b) = (g * k⁻¹, k • b)`, is free. -/
instance instIsCancelSMulProd [MulAction K B] : IsCancelSMul K (RightMul G × B) where
  toIsLeftCancelSMul := inferInstance
  right_cancel' k k' p h := IsCancelSMul.right_cancel k k' p.1 (congrArg Prod.fst h)

end TwistedProduct

variable {G : Type*} [Group G] (K : Subgroup G) (B : Type*) [MulAction K B]

/-- **The twisted product** `G ×_K B`: the balanced product of `G`, with `K` acting by
`k • g = g * k⁻¹`, and `B`, that is, the orbit space of the action
`k • (g, b) = (g * k⁻¹, k • b)` of a subgroup `K` of `G` on `G × B`. -/
abbrev TwistedProduct : Type _ :=
  BalancedProduct K (TwistedProduct.RightMul G) B

namespace TwistedProduct

variable {B}

/-- The class `[g, b]` of `(g, b)` in the twisted product `G ×_K B`. -/
def mk (g : G) (b : B) : TwistedProduct K B :=
  BalancedProduct.mk K (RightMul.mk g) b

variable {K}

/-- Every point of `G ×_K B` is a class `[g, b]`. -/
@[elab_as_elim]
theorem ind {motive : TwistedProduct K B → Prop} (h : ∀ g b, motive (mk K g b))
    (x : TwistedProduct K B) : motive x :=
  Quotient.inductionOn' x fun p ↦ h p.1.val p.2

/-- The projection `G × B → G ×_K B` is surjective. -/
theorem mk_surjective : Surjective fun p : G × B ↦ mk K p.1 p.2 :=
  fun x ↦ ind (motive := fun x ↦ ∃ p : G × B, mk K p.1 p.2 = x) (fun g b ↦ ⟨(g, b), rfl⟩) x

/-- Two classes `[g, b]` and `[g', b']` agree exactly when `(g', b') = (g * k⁻¹, k • b)` for
some `k : K`. -/
theorem mk_eq_mk_iff {g g' : G} {b b' : B} :
    mk K g b = mk K g' b' ↔ ∃ k : K, g' = g * (k : G)⁻¹ ∧ b' = k • b := by
  refine BalancedProduct.mk_eq_mk_iff.trans ⟨fun ⟨k, hg, hb⟩ ↦ ⟨k⁻¹, ?_, ?_⟩,
    fun ⟨k, hg, hb⟩ ↦ ⟨k⁻¹, RightMul.ext ?_, ?_⟩⟩
  · have := congrArg RightMul.val hg
    simp only [RightMul.val_smul, RightMul.val_mk] at this
    simp [← this, mul_assoc]
  · simp [← hb]
  · simp [hg, mul_assoc]
  · simp [hb]

/-- `[g * k, b] = [g, k • b]` for `k : K`. -/
theorem mk_mul_smul (g : G) (k : K) (b : B) : mk K (g * k) b = mk K g (k • b) :=
  mk_eq_mk_iff.2 ⟨k, by simp, rfl⟩

/-- **Maps out of `G ×_K B`.** A map `f : G → B → X` with `f (g * k⁻¹) (k • b) = f g b` for
`k : K` descends to the map `[g, b] ↦ f g b` on the twisted product. -/
def lift {X : Sort*} (f : G → B → X) (hf : ∀ (k : K) g b, f (g * (k : G)⁻¹) (k • b) = f g b) :
    TwistedProduct K B → X :=
  Quotient.lift (fun p : RightMul G × B ↦ f p.1.val p.2) fun _ _ ⟨k, hk⟩ ↦ by
    rw [← hk]
    exact hf k _ _

/-- The descended map sends `[g, b]` to `f g b`. -/
@[simp]
theorem lift_mk {X : Sort*} (f : G → B → X)
    (hf : ∀ (k : K) g b, f (g * (k : G)⁻¹) (k • b) = f g b) (g : G) (b : B) :
    lift f hf (mk K g b) = f g b :=
  (rfl)

/-- Maps out of `G ×_K B` agreeing on every class `[g, b]` are equal. -/
theorem hom_ext {X : Sort*} {φ ψ : TwistedProduct K B → X}
    (h : ∀ g b, φ (mk K g b) = ψ (mk K g b)) : φ = ψ :=
  funext fun x ↦ ind (motive := fun x ↦ φ x = ψ x) h x

/-- **Uniqueness of the descended map.** A map `φ` out of `G ×_K B` with `φ [g, b] = f g b` is
`lift f hf`. -/
theorem lift_unique {X : Sort*} (f : G → B → X)
    (hf : ∀ (k : K) g b, f (g * (k : G)⁻¹) (k • b) = f g b) {φ : TwistedProduct K B → X}
    (h : ∀ g b, φ (mk K g b) = f g b) : φ = lift f hf :=
  hom_ext fun g b ↦ (h g b).trans (lift_mk f hf g b).symm

/-- The scalar multiplication `g • [g', b] = [g * g', b]` of `G` on `G ×_K B`. -/
instance instSMul : SMul G (TwistedProduct K B) where
  smul g := lift (fun g' b ↦ mk K (g * g') b) fun k g' b ↦ by
    rw [← mul_assoc, mk_eq_mk_iff]
    exact ⟨k⁻¹, by simp [mul_assoc], by simp⟩

/-- `g • [g', b] = [g * g', b]`. -/
@[simp]
theorem smul_mk (g g' : G) (b : B) : g • mk K g' b = mk K (g * g') b :=
  (rfl)

/-- The left action `g • [g', b] = [g * g', b]` of `G` on `G ×_K B`. -/
instance instMulAction : MulAction G (TwistedProduct K B) where
  one_smul x := ind (motive := fun x ↦ (1 : G) • x = x) (fun g b ↦ by rw [smul_mk, one_mul]) x
  mul_smul g g' x := ind (motive := fun x ↦ (g * g') • x = g • g' • x)
    (fun g'' b ↦ by rw [smul_mk, smul_mk, smul_mk, mul_assoc]) x

/-- The projection `[g, b] ↦ [g]` of `G ×_K B` onto the orbit space `G ×_K pt` of the right
action of `K` on `G` by multiplication, the space of cosets `gK`. -/
def proj : TwistedProduct K B → TwistedProduct K Unit :=
  BalancedProduct.mapRight (fun _ ↦ ()) fun _ _ ↦ rfl

/-- The projection sends `[g, b]` to `[g]`. -/
@[simp]
theorem proj_mk (g : G) (b : B) : proj (mk K g b) = mk K g () :=
  BalancedProduct.mapRight_mk _ _ _ _

/-- The projection is `G`-equivariant. -/
@[simp]
theorem proj_smul (g : G) (x : TwistedProduct K B) : proj (g • x) = g • proj x :=
  ind (motive := fun x ↦ proj (g • x) = g • proj x)
    (fun _ _ ↦ by rw [smul_mk, proj_mk, proj_mk, smul_mk]) x

/-- The zero section `[g] ↦ [g, b₀]` of `G ×_K B` over `G ×_K pt`, for a point `b₀` of `B`
fixed by `K`. -/
def zeroSection {b₀ : B} (hb₀ : b₀ ∈ MulAction.fixedPoints K B) :
    TwistedProduct K Unit → TwistedProduct K B :=
  BalancedProduct.mapRight (fun _ ↦ b₀) fun k _ ↦ (hb₀ k).symm

variable {b₀ : B} (hb₀ : b₀ ∈ MulAction.fixedPoints K B)

/-- The zero section sends `[g]` to `[g, b₀]`. -/
@[simp]
theorem zeroSection_mk (g : G) (u : Unit) : zeroSection hb₀ (mk K g u) = mk K g b₀ :=
  BalancedProduct.mapRight_mk _ _ _ _

/-- The zero section is a section of the projection. -/
theorem proj_zeroSection : LeftInverse proj (zeroSection hb₀) :=
  fun x ↦ ind (motive := fun x ↦ proj (zeroSection hb₀ x) = x)
    (fun _ _ ↦ by rw [zeroSection_mk, proj_mk]) x

/-- The zero section is `G`-equivariant. -/
@[simp]
theorem zeroSection_smul (g : G) (x : TwistedProduct K Unit) :
    zeroSection hb₀ (g • x) = g • zeroSection hb₀ x :=
  ind (motive := fun x ↦ zeroSection hb₀ (g • x) = g • zeroSection hb₀ x)
    (fun _ _ ↦ by rw [smul_mk, zeroSection_mk, zeroSection_mk, smul_mk]) x

/-- The zero section identifies `G ×_K pt` with the `G`-orbit of `[1, b₀]`. -/
theorem range_zeroSection : range (zeroSection hb₀) = MulAction.orbit G (mk K 1 b₀) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    induction y using ind with
    | h g u => exact ⟨g, by simp⟩
  · rintro ⟨g, rfl⟩
    exact ⟨mk K g (), by simp⟩

section Topology

variable [TopologicalSpace G] [TopologicalSpace B]

/-- The action of a closed subgroup `K` on `G × B` by `k • (g, b) = (g * k⁻¹, k • b)` is
proper. Along an ultrafilter on which `(g * k⁻¹, g)` converges, `k = (g * k⁻¹)⁻¹ * g` converges
in `G`, and its limit lies in `K` because `K` is closed. -/
instance instProperSMulProd [IsTopologicalGroup G] [hK : IsClosed (K : Set G)]
    [ContinuousSMul K B] [T2Space B] : ProperSMul K (RightMul G × B) := by
  -- `RightMul G` is `G` with its topology, and `k • (g, b)` is `(g * k⁻¹, k • b)` by
  -- definition (`RightMul.val_smul`), so the action map is this map of products.
  have hcont : Continuous fun p : K × (RightMul G × B) ↦ p.1 • p.2 :=
    show Continuous fun p : K × (G × B) ↦ (p.2.1 * (p.1 : G)⁻¹, p.1 • p.2.2) by fun_prop
  refine properSMul_iff_continuousSMul_ultrafilter_tendsto.2 ⟨⟨hcont⟩, fun 𝒰 x₁ x₂ h ↦ ?_⟩
  have h₁ := h.fst_nhds
  have h₂ := h.snd_nhds
  -- The element `k` of `K` is `(g * k⁻¹)⁻¹ * g`.
  have hk : Tendsto (fun p : K × (RightMul G × B) ↦ ((p.1 : K) : G)) 𝒰
      (𝓝 (x₁.1.val⁻¹ * x₂.1.val)) := by
    refine ((RightMul.continuous_val.tendsto _).comp h₁.fst_nhds).inv.mul
      ((RightMul.continuous_val.tendsto _).comp h₂.fst_nhds) |>.congr fun p ↦ ?_
    simp [mul_assoc]
  have hmem : x₁.1.val⁻¹ * x₂.1.val ∈ K :=
    hK.mem_of_tendsto hk (Eventually.of_forall fun p ↦ p.1.property)
  have hfst : Tendsto Prod.fst 𝒰 (𝓝 (⟨_, hmem⟩ : K)) :=
    (tendsto_subtype_rng (f := (Prod.fst : K × (RightMul G × B) → K))).2 hk
  refine ⟨⟨_, hmem⟩, Prod.ext (RightMul.ext ?_) ?_, hfst⟩
  · simp
  · exact tendsto_nhds_unique (hfst.smul h₂.snd_nhds) h₁.snd_nhds

end Topology

section Manifold

variable {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
  {HK : Type*} [TopologicalSpace HK] {IK : ModelWithCorners ℝ EK HK}
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] {IG : ModelWithCorners ℝ EG HG}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}

variable [TopologicalSpace G] [ChartedSpace HG G] [ChartedSpace HK K]
  [TopologicalSpace B] [ChartedSpace HB B]

/-- A smooth action of `K` on `B` gives a smooth action of `K` on pairs: the inclusion of `K`
in `G` is smooth by automatic smoothness (`TauCeti.Lie.contMDiff_of_continuous_monoidHom`). -/
instance instContMDiffSMulProd [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EK]
    [LieGroup IG ∞ G] [LieGroup IK ∞ K] [ContMDiffSMul IK IB ∞ K B] :
    ContMDiffSMul IK (IG.prod IB) ∞ K (RightMul G × B) where
  contMDiff_smul := by
    have hι : ContMDiff IK IG ∞ (Subtype.val : K → G) :=
      Lie.contMDiff_of_continuous_monoidHom K.subtype continuous_subtypeVal
    -- `RightMul G` is the manifold `G`, and `k • (g, b)` is `(g * k⁻¹, k • b)` by definition
    -- (`RightMul.val_smul`), so the action map is this map of products.
    exact show ContMDiff (IK.prod (IG.prod IB)) (IG.prod IB) ∞
        (fun p : K × (G × B) ↦ (p.2.1 * (p.1 : G)⁻¹, p.1 • p.2.2)) from
      (contMDiff_snd.fst.mul (hι.comp contMDiff_fst).inv).prodMk
        (contMDiff_fst.smul contMDiff_snd.snd)

variable [FiniteDimensional ℝ EK] [LieGroup IK ∞ K]
  [FiniteDimensional ℝ EG] [IG.Boundaryless] [LieGroup IG ∞ G]
  [FiniteDimensional ℝ EB] [IB.Boundaryless] [IsManifold IB ∞ B] [T2Space B]
  [ContMDiffSMul IK IB ∞ K B]

variable (K B IK IG IB) in
/-- The smooth structure of the twisted product `G ×_K B`, from the quotient manifold theorem
for the free proper action of `K` on `G × B`. It is a manifold
(`TauCeti.TwistedProduct.instIsManifold`) of dimension `dim G + dim B - dim K`, modelled on
`ProperSMul.QuotientModelSpace EK (EG × EB)`. -/
abbrev chartedSpace :
    ChartedSpace (ProperSMul.QuotientModelSpace EK (EG × EB)) (TwistedProduct K B) :=
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG ∞
  letI : T2Space G := IG.t2Space_of_lieGroup ∞
  letI : ContinuousSMul K B := ContMDiffSMul.continuousSMul (I := IK) (I' := IB) ∞
  haveI : IsClosed (K : Set G) := Lie.isClosed_of_chartedSpace IK
  ProperSMul.orbitRelQuotientChartedSpace IK K (IG.prod IB) (RightMul G × B)

/-- **The twisted product `G ×_K B` is a smooth manifold.** -/
instance instIsManifold :
    let _ := chartedSpace K B IK IG IB
    IsManifold 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB)) ∞ (TwistedProduct K B) :=
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG ∞
  letI : T2Space G := IG.t2Space_of_lieGroup ∞
  letI : ContinuousSMul K B := ContMDiffSMul.continuousSMul (I := IK) (I' := IB) ∞
  haveI : IsClosed (K : Set G) := Lie.isClosed_of_chartedSpace IK
  ProperSMul.instIsManifoldOrbitRelQuotient

/-- **The projection `G × B → G ×_K B` is a smooth submersion.** -/
theorem isSubmersion_mk :
    let _ := chartedSpace K B IK IG IB
    IsSubmersion (IG.prod IB) 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB)) ∞
      fun p : G × B ↦ mk K p.1 p.2 :=
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup IG ∞
  let _ : T2Space G := IG.t2Space_of_lieGroup ∞
  let _ : ContinuousSMul K B := ContMDiffSMul.continuousSMul (I := IK) (I' := IB) ∞
  have : IsClosed (K : Set G) := Lie.isClosed_of_chartedSpace IK
  have h := ProperSMul.isSubmersion_quotientMk (I := IK) (G := K) (I' := IG.prod IB)
    (M := RightMul G × B)
  h

/-- The projection `G × B → G ×_K B` is smooth. -/
theorem contMDiff_mk :
    let _ := chartedSpace K B IK IG IB
    ContMDiff (IG.prod IB) 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB)) ∞
      fun p : G × B ↦ mk K p.1 p.2 := by
  let _ := chartedSpace K B IK IG IB
  exact isSubmersion_mk.contMDiff

/-- **The left action of `G` on `G ×_K B` is smooth.** It descends from the smooth map
`(g, (g', b)) ↦ [g * g', b]` along the surjective submersion `G × (G × B) → G × (G ×_K B)`. -/
theorem contMDiffSMul :
    let _ := chartedSpace K B IK IG IB
    ContMDiffSMul IG 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB)) ∞ G
      (TwistedProduct K B) := by
  let _ := chartedSpace K B IK IG IB
  have hq := (IsSubmersion.id (I := IG) (M := G) (n := ∞)).prodMap
    (isSubmersion_mk (K := K) (B := B) (IK := IK) (IG := IG) (IB := IB))
  refine ⟨(hq.contMDiff_comp_iff (surjective_id.prodMap mk_surjective) le_rfl).1 ?_⟩
  exact contMDiff_mk.comp ((contMDiff_fst.mul contMDiff_snd.fst).prodMk contMDiff_snd.snd)

/-- **The projection `G ×_K B → G ×_K pt` is smooth.** -/
theorem contMDiff_proj :
    let _ := chartedSpace K B IK IG IB
    let _ := chartedSpace K Unit IK IG 𝓘(ℝ, Unit)
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB))
      𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × Unit)) ∞ (proj : TwistedProduct K B → _) := by
  let _ := chartedSpace K B IK IG IB
  let _ := chartedSpace K Unit IK IG 𝓘(ℝ, Unit)
  refine ((isSubmersion_mk (K := K) (B := B) (IK := IK) (IG := IG) (IB := IB)).contMDiff_comp_iff
    mk_surjective le_rfl).1 ?_
  have h : (proj ∘ fun p : G × B ↦ mk K p.1 p.2) = fun p ↦ mk K p.1 () :=
    funext fun p ↦ proj_mk p.1 p.2
  rw [h]
  exact contMDiff_mk.comp (contMDiff_fst.prodMk contMDiff_const)

/-- The zero section `G ×_K pt → G ×_K B` at a `K`-fixed point is smooth. -/
theorem contMDiff_zeroSection :
    let _ := chartedSpace K B IK IG IB
    let _ := chartedSpace K Unit IK IG 𝓘(ℝ, Unit)
    ContMDiff 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × Unit))
      𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB)) ∞ (zeroSection hb₀) := by
  let _ := chartedSpace K B IK IG IB
  let _ := chartedSpace K Unit IK IG 𝓘(ℝ, Unit)
  refine ((isSubmersion_mk (K := K) (B := Unit) (IK := IK) (IG := IG)
    (IB := 𝓘(ℝ, Unit))).contMDiff_comp_iff mk_surjective le_rfl).1 ?_
  have h : (zeroSection hb₀ ∘ fun p : G × Unit ↦ mk K p.1 p.2) = fun p ↦ mk K p.1 b₀ :=
    funext fun p ↦ zeroSection_mk hb₀ p.1 p.2
  rw [h]
  exact contMDiff_mk.comp (contMDiff_fst.prodMk contMDiff_const)

/-- **The zero section is a smooth embedding.** For a point `b₀` of `B` fixed by `K`, the map
`G ×_K pt → G ×_K B`, `[g] ↦ [g, b₀]`, is a smooth embedding onto the `G`-orbit of `[1, b₀]`
(`TauCeti.TwistedProduct.range_zeroSection`): it has the smooth left inverse `proj`. -/
theorem isSmoothEmbedding_zeroSection :
    let _ := chartedSpace K B IK IG IB
    let _ := chartedSpace K Unit IK IG 𝓘(ℝ, Unit)
    IsSmoothEmbedding 𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × Unit))
      𝓘(ℝ, ProperSMul.QuotientModelSpace EK (EG × EB)) ∞ (zeroSection hb₀) := by
  let _ := chartedSpace K B IK IG IB
  let _ := chartedSpace K Unit IK IG 𝓘(ℝ, Unit)
  exact (contMDiff_zeroSection (IK := IK) (IG := IG) (IB := IB) hb₀
    ).isSmoothEmbedding_of_leftInverse (by simp)
    ((contMDiff_proj (IK := IK) (IG := IG) (IB := IB)).of_le (by simp)) (proj_zeroSection hb₀)

end Manifold

end TwistedProduct

end TauCeti
