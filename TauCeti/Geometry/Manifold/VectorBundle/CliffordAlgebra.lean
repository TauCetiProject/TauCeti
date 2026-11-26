/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.CliffordAlgebra.IsometryAction
public import TauCeti.Geometry.Manifold.VectorBundle.OrthonormalFrame
import TauCeti.Geometry.Manifold.FiberBundle.Associated.Map
import TauCeti.Geometry.Manifold.FiberBundle.Associated.Principal
import TauCeti.Geometry.Manifold.VectorBundle.Associated.Bilinear
public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# The real Clifford algebra bundle of a Riemannian vector bundle

The orthonormal frame bundle acts on the negative Clifford algebra of the model fibre.
Its associated vector bundle has fibrewise Clifford multiplication, unit, conjugation and
grade involution. The canonical identification with the negative Clifford algebra of each
actual fibre sends the class of an element in a frame to its image under that frame's
Clifford algebra map. In particular, the fibrewise generator inclusion is independent of frames.

The model metric is the scalar-part Euclidean metric on the Clifford algebra. The bundle
uses the native associated vector bundle and the orthonormal frame bundle of
`TauCeti.OrthonormalFrameBundle`.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, §12.1.5.
-/

public noncomputable section

open Bundle MulOpposite
open scoped Manifold ContDiff CliffordAlgebra.NegativeMetric

namespace TauCeti

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E]
  (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fact (Module.finrank ℝ V = Module.finrank ℝ F)]

local notation "OG" => unitary (V →L[ℝ] V)
local notation "C" => CliffordAlgebra (negNormSqForm V)
local notation "Fr" => OrthonormalFrameBundle.Fiber ℝ F E V

variable (F) in
/-- The real negative Clifford algebra bundle associated to the orthonormal frame bundle.
It has as model fibre the Clifford algebra of the negative squared norm on `V`. -/
abbrev CliffordAlgebraBundle : B → Type _ := AssociatedBundle OG Fr C

namespace CliffordAlgebraBundle

variable {E V}

-- The associated fibre is a type synonym of the model algebra. Its atlas transitions are
-- algebra automorphisms, as witnessed by `frameAlgEquiv`.
instance instRing (b : B) : Ring (CliffordAlgebraBundle F E V b) :=
  inferInstanceAs (Ring C)

instance instAlgebra (b : B) : Algebra ℝ (CliffordAlgebraBundle F E V b) :=
  inferInstanceAs (Algebra ℝ C)

instance instStarRing (b : B) : StarRing (CliffordAlgebraBundle F E V b) :=
  inferInstanceAs (StarRing C)

/-- An orthonormal frame identifies the model Clifford algebra with the associated fibre
over its base point. -/
def frameAlgEquiv {b : B} (p : Fr b) : C ≃ₐ[ℝ] CliffordAlgebraBundle F E V b :=
  AlgEquiv.ofLinearEquiv (AssociatedBundle.mkContinuousLinearEquiv ℝ OG p).toLinearEquiv
    (by
      simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
        AssociatedBundle.mkContinuousLinearEquiv_apply, AssociatedBundle.mk_def,
        Unitary.smul_clifford_eq]
      exact map_one (Unitary.cliffordAlgEquiv _))
    (fun x y ↦ by
      simp only [ContinuousLinearEquiv.coe_toLinearEquiv,
        AssociatedBundle.mkContinuousLinearEquiv_apply, AssociatedBundle.mk_def,
        Unitary.smul_clifford_eq]
      exact map_mul (Unitary.cliffordAlgEquiv _) x y)

@[simp]
theorem frameAlgEquiv_apply {b : B} (p : Fr b) (x : C) :
    frameAlgEquiv p x = AssociatedBundle.mk OG p x := by
  -- The algebra equivalence has the forward map of the associated linear equivalence.
  change AssociatedBundle.mkContinuousLinearEquiv ℝ OG p x = _
  exact AssociatedBundle.mkContinuousLinearEquiv_apply p x

@[simp]
theorem star_mk {b : B} (p : Fr b) (x : C) :
    star (AssociatedBundle.mk OG p x) = AssociatedBundle.mk OG p (star x) := by
  simp only [AssociatedBundle.mk_def, Unitary.smul_clifford_eq]
  rw [Unitary.cliffordAlgEquiv_def]
  exact (CliffordAlgebra.map_star
    (Unitary.linearIsometryEquiv _).negNormSqFormIsometryEquiv.toIsometry x).symm

/-- The canonical algebra identification of the associated fibre with the Clifford algebra
of the negative squared norm on the actual fibre. -/
def fiberAlgEquiv (b : B) : CliffordAlgebraBundle F E V b ≃ₐ[ℝ]
    CliffordAlgebra (negNormSqForm (E b)) :=
  let p := (FiberBundle.homeomorphAt OG Fr b).symm 1
  (frameAlgEquiv p).symm.trans
    (CliffordAlgebra.equivOfIsometry p.frame.negNormSqFormIsometryEquiv)

/-- The canonical identification applies the given frame to all Clifford generators. -/
@[simp]
theorem fiberAlgEquiv_mk {b : B} (p : Fr b) (x : C) :
    fiberAlgEquiv b (AssociatedBundle.mk OG p x) =
      CliffordAlgebra.equivOfIsometry p.frame.negNormSqFormIsometryEquiv x := by
  let p₀ := (FiberBundle.homeomorphAt OG Fr b).symm 1
  let g := PrincipalBundle.division OG p₀ p
  have hp : (Unitary.linearIsometryEquiv g).trans p₀.frame = p.frame := by
    dsimp only [g]
    rw [OrthonormalFrameBundle.division_eq, MulEquiv.apply_symm_apply]
    ext v
    simp
  have hc : AssociatedBundle.mk OG p x = frameAlgEquiv p₀ (g • x) := by
    rw [frameAlgEquiv_apply]
    exact ((AssociatedBundle.mk_eq_mk_iff (p := p₀) (q := p)).2 rfl).symm
  dsimp only [fiberAlgEquiv, AlgEquiv.trans_apply]
  rw [hc, AlgEquiv.symm_apply_apply, Unitary.smul_clifford_eq, Unitary.cliffordAlgEquiv_def,
    ← AlgEquiv.trans_apply, CliffordAlgebra.equivOfIsometry_trans,
    ← LinearIsometryEquiv.negNormSqFormIsometryEquiv_trans, hp]

/-- The fibre's Clifford norm is the intrinsic scalar-part norm of its image. -/
theorem norm_eq_regularNorm (b : B) (x : CliffordAlgebraBundle F E V b) :
    ‖x‖ = CliffordAlgebra.regularNorm _ (fiberAlgEquiv b x) := by
  obtain ⟨p, y, rfl⟩ := AssociatedBundle.exists_mk (G := ↥OG) (P := Fr) (F := C) x
  rw [AssociatedBundle.norm_mk, fiberAlgEquiv_mk, CliffordAlgebra.regularNorm_equivOfIsometry,
    CliffordAlgebra.NegativeMetric.norm_eq_regularNorm]

/-- Clifford multiplication has a uniform bound in the fibre metric, with a constant from the
model Clifford algebra. -/
theorem exists_norm_mul_le :
    ∃ K : ℝ, 0 < K ∧ ∀ (b : B) (x y : CliffordAlgebraBundle F E V b),
      ‖x * y‖ ≤ K * ‖x‖ * ‖y‖ := by
  obtain ⟨K, hK, hmul⟩ := CliffordAlgebra.exists_regularNorm_mul_le
    (negNormSqForm V) (posDef_neg_negNormSqForm V)
  refine ⟨K, hK, fun b x y ↦ ?_⟩
  let p := (FiberBundle.homeomorphAt OG Fr b).symm 1
  obtain ⟨u, rfl⟩ := (frameAlgEquiv p).surjective x
  obtain ⟨v, rfl⟩ := (frameAlgEquiv p).surjective y
  rw [← map_mul]
  simpa only [frameAlgEquiv_apply, AssociatedBundle.norm_mk,
    CliffordAlgebra.NegativeMetric.norm_eq_regularNorm] using hmul u v

/-- The canonical linear inclusion of a bundle fibre into its Clifford algebra. -/
def ι (b : B) : E b →ₗ[ℝ] CliffordAlgebraBundle F E V b :=
  (fiberAlgEquiv b).symm.toLinearMap.comp (CliffordAlgebra.ι (negNormSqForm (E b)))

@[simp]
theorem fiberAlgEquiv_ι (b : B) (v : E b) :
    fiberAlgEquiv b (ι (F := F) (V := V) b v) = CliffordAlgebra.ι (negNormSqForm (E b)) v := by
  simp [ι]

/-- In an orthonormal frame, fibrewise Clifford inclusion is the model generator inclusion. -/
@[simp]
theorem ι_frame {b : B} (p : Fr b) (v : V) :
    ι (F := F) (E := E) (V := V) b (p.frame v) =
      AssociatedBundle.mk OG p (CliffordAlgebra.ι (negNormSqForm V) v) := by
  apply (fiberAlgEquiv b).injective
  simp [ι, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]

/-- The fibrewise generator squares to minus the squared length times the unit. -/
@[simp]
theorem ι_sq (b : B) (v : E b) :
    ι (F := F) (V := V) b v ^ 2 = algebraMap ℝ (CliffordAlgebraBundle F E V b) (-‖v‖ ^ 2) := by
  apply (fiberAlgEquiv b).injective
  simp [ι, pow_two, CliffordAlgebra.ι_sq_scalar]

/-- Algebra homomorphisms from a Clifford fibre agree if they agree on the generating vectors. -/
@[ext]
theorem algHom_ext {S : Type*} [Semiring S] [Algebra ℝ S] {b : B}
    {f g : CliffordAlgebraBundle F E V b →ₐ[ℝ] S}
    (h : ∀ v : E b, f (ι (F := F) (V := V) b v) = g (ι (F := F) (V := V) b v)) : f = g := by
  let e := (fiberAlgEquiv (F := F) (E := E) (V := V) b).symm
  have he : f.comp e.toAlgHom = g.comp e.toAlgHom := by
    apply CliffordAlgebra.hom_ext
    ext v
    exact h v
  exact AlgHom.ext fun x ↦ by
    obtain ⟨y, rfl⟩ := e.surjective x
    exact AlgHom.congr_fun he y

/-- The fibrewise Clifford algebra has the usual dimension, including dimension one in rank zero. -/
@[simp]
theorem finrank_eq (b : B) :
    Module.finrank ℝ (CliffordAlgebraBundle F E V b) = 2 ^ Module.finrank ℝ V := by
  rw [AssociatedBundle.finrank_eq, CliffordAlgebra.finrank_eq_two_pow]

/-- The grade involution on each fibre, acting by minus one on generators. -/
def involute (b : B) : CliffordAlgebraBundle F E V b ≃ₐ[ℝ] CliffordAlgebraBundle F E V b :=
  (fiberAlgEquiv b).trans (CliffordAlgebra.involuteEquiv.trans (fiberAlgEquiv b).symm)

@[simp]
theorem involute_frame {b : B} (p : Fr b) (x : C) :
    involute b (AssociatedBundle.mk OG p x) =
      AssociatedBundle.mk OG p (CliffordAlgebra.involute x) := by
  apply (fiberAlgEquiv b).injective
  simp [involute, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_involute]

@[simp]
theorem involute_ι (b : B) (v : E b) :
    involute b (ι (F := F) (E := E) (V := V) b v) = -ι (F := F) (E := E) (V := V) b v := by
  apply (fiberAlgEquiv b).injective
  simp [involute, ι]

section Smooth

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  {n : ℕ∞ω}

local notation "A" => CliffordAlgebraBundle F E V

private theorem mulCLM_equivariant (g : OG) (x y : C) :
    CliffordAlgebra.NegativeMetric.mulCLM V (g • x) (g • y) =
      g • CliffordAlgebra.NegativeMetric.mulCLM V x y := by
  simp only [CliffordAlgebra.NegativeMetric.mulCLM_apply, Unitary.smul_clifford_eq, map_mul]

/-- Clifford multiplication, viewed as a continuous bilinear map on each fibre. -/
def mulCLM (b : B) : A b →L[ℝ] A b →L[ℝ] A b :=
  AssociatedBundle.bilinearMap (CliffordAlgebra.NegativeMetric.mulCLM V)
    (mulCLM_equivariant (V := V)) b

@[simp]
theorem mulCLM_apply (b : B) (x y : A b) : mulCLM b x y = x * y := by
  let p := (FiberBundle.homeomorphAt OG Fr b).symm 1
  obtain ⟨u, rfl⟩ := (frameAlgEquiv p).surjective x
  obtain ⟨v, rfl⟩ := (frameAlgEquiv p).surjective y
  rw [← map_mul, frameAlgEquiv_apply, frameAlgEquiv_apply, frameAlgEquiv_apply]
  exact (AssociatedBundle.bilinearMap_mk _ _ p u v).trans
    (congrArg (AssociatedBundle.mk OG p) (CliffordAlgebra.NegativeMetric.mulCLM_apply V u v))

/-- Clifford multiplication is a smooth section of the iterated Hom bundle. -/
theorem contMDiff_mulCLM :
    ContMDiff IB (IB.prod 𝓘(ℝ, C →L[ℝ] C →L[ℝ] C)) n
      (fun b ↦ TotalSpace.mk' (C →L[ℝ] C →L[ℝ] C) (E := fun b ↦ A b →L[ℝ] A b →L[ℝ] A b)
        b (mulCLM b)) :=
  AssociatedBundle.contMDiff_bilinearMap _ _

/-- The Clifford unit is a smooth section. -/
theorem contMDiff_one :
    ContMDiff IB (IB.prod 𝓘(ℝ, C)) n (fun b ↦ (⟨b, 1⟩ : TotalSpace C A)) := by
  intro b₀
  rw [contMDiffAt_section_iff]
  refine (contMDiffAt_const (c := (1 : C))).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt OG Fr b₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt OG Fr b₀)] with b hb
  let p := (FiberBundle.homeomorphAt OG Fr b).symm 1
  rw [← map_one (frameAlgEquiv p), frameAlgEquiv_apply,
    AssociatedBundle.trivializationAt_mk_snd hb, Unitary.smul_clifford_eq, map_one]

private def ιEquivariant : V →[OG] C where
  toFun := CliffordAlgebra.ι (negNormSqForm V)
  map_smul' g v := (Unitary.cliffordAlgEquiv_ι g v).symm

variable [ENat.LEInfty n] [ContMDiffVectorBundle n F E IB] [IsContMDiffRiemannianBundle IB n F E] in
/-- The generator inclusion is smooth on total spaces. -/
theorem contMDiff_ι :
    ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, C)) n
      (fun z : TotalSpace F E ↦ (⟨z.proj, ι (F := F) (V := V) z.proj z.snd⟩ : TotalSpace C A)) := by
  let d := OrthonormalFrameBundle.associatedBundleDiffeomorph n IB F E V
  have hι : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, C) n (ιEquivariant (V := V)) :=
    (CliffordAlgebra.ι (negNormSqForm V)).toContinuousLinearMap.contMDiff
  have h := (ManifoldTotalSpace.contMDiff_homeomorph_symm n C A IB).comp
    ((AssociatedBundle.contMDiff_totalSpaceMap (P := Fr) (IB := IB) ιEquivariant hι).comp
      ((ManifoldTotalSpace.contMDiff_homeomorph n V (AssociatedBundle OG Fr V) IB).comp
        d.symm.contMDiff))
  refine h.congr fun z ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
    Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
  obtain ⟨b, v⟩ := z
  let p := (FiberBundle.homeomorphAt OG Fr b).symm 1
  dsimp only [d]
  rw [OrthonormalFrameBundle.associatedBundleDiffeomorph_symm_mk_apply (n := n) (IB := IB) p v,
    AssociatedBundle.totalSpaceMap_mk]
  -- The equivariant map in this chart is the model generator.
  change (⟨b, ι (F := F) (V := V) b v⟩ : TotalSpace C A) =
    ⟨b, AssociatedBundle.mk OG p (CliffordAlgebra.ι (negNormSqForm V) (p.frame.symm v))⟩
  rw [← ι_frame, p.frame.apply_symm_apply]

private def starEquivariant : C →[OG] C where
  toFun := star
  map_smul' g x := by
    simp only [Unitary.smul_clifford_eq, Unitary.cliffordAlgEquiv_def,
      id_eq, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_star]

private def involuteEquivariant : C →[OG] C where
  toFun := CliffordAlgebra.involute
  map_smul' g x := by
    simp only [Unitary.smul_clifford_eq, Unitary.cliffordAlgEquiv_def,
      id_eq, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_involute]

private theorem contMDiff_inducedCliffordMap (f : C →[OG] C)
    (hf : ContMDiff 𝓘(ℝ, C) 𝓘(ℝ, C) n f) :
    ContMDiff (IB.prod 𝓘(ℝ, C)) (IB.prod 𝓘(ℝ, C)) n
      (AssociatedBundle.totalSpaceMap (P := Fr) f) := by
  have h := (ManifoldTotalSpace.contMDiff_homeomorph_symm n C A IB).comp
    ((AssociatedBundle.contMDiff_totalSpaceMap (P := Fr) (IB := IB) f hf).comp
      (ManifoldTotalSpace.contMDiff_homeomorph n C A IB))
  exact h.congr fun x ↦ by simp only [Function.comp_apply, Homeomorph.symm_apply_apply]

/-- Clifford conjugation is smooth on the algebra bundle. -/
theorem contMDiff_star :
    ContMDiff (IB.prod 𝓘(ℝ, C)) (IB.prod 𝓘(ℝ, C)) n
      (fun z : TotalSpace C A ↦ (⟨z.proj, star z.snd⟩ : TotalSpace C A)) := by
  let f : C →ₗ[ℝ] C :=
    CliffordAlgebra.reverse.comp (CliffordAlgebra.involute (Q := negNormSqForm V)).toLinearMap
  have hf : ContMDiff 𝓘(ℝ, C) 𝓘(ℝ, C) n (starEquivariant (V := V)) :=
    f.toContinuousLinearMap.contMDiff
  refine (contMDiff_inducedCliffordMap (E := E) starEquivariant hf).congr fun ⟨b, x⟩ ↦ ?_
  obtain ⟨p, x, rfl⟩ := AssociatedBundle.exists_mk (G := ↥OG) (P := Fr) (F := C) x
  rw [AssociatedBundle.totalSpaceMap_mk]
  apply congrArg (TotalSpace.mk' C b)
  -- The equivariant map in this chart is model Clifford conjugation.
  change star (AssociatedBundle.mk OG p x) = AssociatedBundle.mk OG p (star x)
  exact star_mk p x

/-- The grade involution is smooth on the algebra bundle. -/
theorem contMDiff_involute :
    ContMDiff (IB.prod 𝓘(ℝ, C)) (IB.prod 𝓘(ℝ, C)) n
      (fun z : TotalSpace C A ↦ (⟨z.proj, involute z.proj z.snd⟩ : TotalSpace C A)) := by
  have hf : ContMDiff 𝓘(ℝ, C) 𝓘(ℝ, C) n (involuteEquivariant (V := V)) :=
    (CliffordAlgebra.involute (Q := negNormSqForm V)).toLinearMap.toContinuousLinearMap.contMDiff
  refine (contMDiff_inducedCliffordMap (E := E) involuteEquivariant hf).congr fun ⟨b, x⟩ ↦ ?_
  obtain ⟨p, x, rfl⟩ := AssociatedBundle.exists_mk (G := ↥OG) (P := Fr) (F := C) x
  rw [AssociatedBundle.totalSpaceMap_mk]
  exact congrArg (TotalSpace.mk' C b) (involute_frame p x)

end Smooth

section Naturality

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {E' : B → Type*} [∀ b, NormedAddCommGroup (E' b)] [∀ b, InnerProductSpace ℝ (E' b)]
  [TopologicalSpace (TotalSpace F' E')] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  [ContinuousFiberNorm F' E'] [Fact (Module.finrank ℝ V = Module.finrank ℝ F')]
  (Φ : ∀ b, E b ≃ₗᵢ[ℝ] E' b)

/-- A fibrewise isometry induces the corresponding algebra equivalence of Clifford fibres. -/
def map (b : B) : CliffordAlgebraBundle F E V b ≃ₐ[ℝ] CliffordAlgebraBundle F' E' V b :=
  (fiberAlgEquiv b).trans
    ((CliffordAlgebra.equivOfIsometry (Φ b).negNormSqFormIsometryEquiv).trans
      (fiberAlgEquiv b).symm)

@[simp]
theorem map_mk {b : B} (p : Fr b) (x : C) :
    map Φ b (AssociatedBundle.mk OG p x) =
      AssociatedBundle.mk OG (OrthonormalFrameBundle.Fiber.map (F' := F') Φ p) x := by
  apply (fiberAlgEquiv b).injective
  rw [map, AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    fiberAlgEquiv_mk, fiberAlgEquiv_mk, OrthonormalFrameBundle.Fiber.frame_map,
    LinearIsometryEquiv.negNormSqFormIsometryEquiv_trans, ← CliffordAlgebra.equivOfIsometry_trans]
  rfl

@[simp]
theorem map_ι (b : B) (v : E b) :
    map Φ b (ι (F := F) (V := V) b v) = ι (F := F') (V := V) b (Φ b v) := by
  let p := (FiberBundle.homeomorphAt OG Fr b).symm 1
  obtain ⟨w, rfl⟩ := p.frame.surjective v
  rw [ι_frame, map_mk, ← ι_frame]
  simp

/-- An isometry of the generating fibres is isometric for the Clifford bundle metrics. -/
theorem norm_map (b : B) (x : CliffordAlgebraBundle F E V b) :
    ‖map (F' := F') Φ b x‖ = ‖x‖ := by
  obtain ⟨p, v, rfl⟩ := AssociatedBundle.exists_mk (G := ↥OG) (P := Fr) (F := C) x
  simp only [map_mk, AssociatedBundle.norm_mk]

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n F E IB]
  [IsContMDiffRiemannianBundle IB n F E] [ContMDiffVectorBundle n F' E' IB]
  [IsContMDiffRiemannianBundle IB n F' E']

/-- A smooth isometry of Riemannian vector bundles induces a smooth map of Clifford bundles. -/
theorem contMDiff_map
    (hΦ : ContMDiff (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F')) n
      (fun z : TotalSpace F E ↦ (⟨z.proj, Φ z.proj z.snd⟩ : TotalSpace F' E'))) :
    ContMDiff (IB.prod 𝓘(ℝ, C)) (IB.prod 𝓘(ℝ, C)) n
      (fun z : TotalSpace C (CliffordAlgebraBundle F E V) ↦
        (⟨z.proj, map Φ z.proj z.snd⟩ : TotalSpace C (CliffordAlgebraBundle F' E' V))) := by
  let e := AssociatedBundle.diffeomorphOfEquivariant (n := n) (IB := IB) (F := C) (IF := 𝓘(ℝ, C))
    (IG := Unitary.model (V →L[ℝ] V)) (IH := Unitary.model (V →L[ℝ] V))
    (P := Fr) (Q := OrthonormalFrameBundle.Fiber ℝ F' E' V)
    (MonoidHom.id (↥OG)) (fun _ ↦ OrthonormalFrameBundle.Fiber.map Φ)
    (fun _ p g ↦ by
      simpa only [MonoidHom.id_apply] using
        OrthonormalFrameBundle.Fiber.map_smul (F := F) (F' := F') Φ (op g) p)
    (by
      rw [← ManifoldTotalSpace.fiberwiseMap_eq]
      exact OrthonormalFrameBundle.contMDiff_fiberwiseMap_map (V := V) hΦ)
    (fun _ _ ↦ rfl)
  have h := (ManifoldTotalSpace.contMDiff_homeomorph_symm n C
    (CliffordAlgebraBundle F' E' V) IB).comp
    (e.contMDiff.comp (ManifoldTotalSpace.contMDiff_homeomorph n C
      (CliffordAlgebraBundle F E V) IB))
  refine h.congr fun ⟨b, x⟩ ↦ ?_
  obtain ⟨p, v, rfl⟩ := AssociatedBundle.exists_mk (G := ↥OG) (P := Fr) (F := C) x
  simp only [Function.comp_apply, e, AssociatedBundle.diffeomorphOfEquivariant_mk,
    Homeomorph.symm_apply_apply, map_mk]

end Naturality

end CliffordAlgebraBundle

end TauCeti
