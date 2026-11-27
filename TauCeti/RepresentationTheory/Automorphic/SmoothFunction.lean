/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Geometry.Manifold.Algebra.ComplexSmoothFunctions
public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.Topology.Algebra.Group.ContinuousAut.CompactOpenSubgroup

/-!
# Smooth functions of finite adelic level

On a product `G∞ × Gf`, a complex-valued function is smooth of finite adelic level if its
archimedean slices are smooth and a single compact open subgroup of `Gf` fixes it under right
translation. At level `J` the functions are families of smooth functions indexed by the
cosets `xJ`. Intersections of compact open subgroups give common refinements, so the union
of the levels is an algebra. These spaces are the function carriers on which to impose
growth conditions and act by finite Hecke operators.

Right translation acts by `R(y)f(x) = f(xy)`. It carries level `J` to level
`y_f J y_f⁻¹` and preserves left invariance under a subgroup of the product.

## References

* A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*, Corvallis
  proceedings I, Proc. Sympos. Pure Math. **33** (1979), §4.1.
* J. Getz, *An introduction to automorphic representations*, Definition 6.12.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [Group F]

namespace AdelicSmoothFunction

/-- Families of smooth archimedean slices at level `J`, viewed before passing to the finite
quotient. -/
def level (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (J : Subgroup F) : Subalgebra ℂ (F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) where
  carrier := {f | ∀ (x : F) (j : J), f (x * j) = f x}
  mul_mem' hf hg x j := by simp only [Pi.mul_apply, hf x j, hg x j]
  add_mem' hf hg x j := by simp only [Pi.add_apply, hf x j, hg x j]
  algebraMap_mem' z x j := by simp

@[simp]
theorem mem_level_iff {J : Subgroup F} {f : F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    f ∈ level I M J ↔ ∀ (x : F) (j : J), f (x * j) = f x := by rfl

/-- Shrinking the level enlarges the algebra of invariant functions. -/
theorem level_antitone : Antitone (level I M : Subgroup F → _) :=
  fun _ _ h _ hf ↦ mem_level_iff.mpr fun x j ↦ mem_level_iff.mp hf x ⟨j, h j.property⟩

/-- Functions at level `J` are exactly smooth families on the finite-adelic coset space.
The forward map from families is pullback along the quotient. -/
def quotientLevelEquiv (J : Subgroup F) :
    (F ⧸ J → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) ≃ₐ[ℂ] level I M J where
  toFun f := ⟨fun x ↦ f (QuotientGroup.mk x), mem_level_iff.mpr fun x j ↦
    congrArg f (QuotientGroup.mk_mul_of_mem x j.property)⟩
  invFun f := Quotient.lift f.val fun x y h ↦ by
    have hj : x⁻¹ * y ∈ J := QuotientGroup.leftRel_apply.mp h
    simpa using (mem_level_iff.mp f.property x ⟨x⁻¹ * y, hj⟩).symm
  left_inv f := funext fun q ↦ Quotient.inductionOn q fun _ ↦ rfl
  right_inv f := Subtype.ext rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem quotientLevelEquiv_apply (J : Subgroup F)
    (f : F ⧸ J → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : F) :
    (quotientLevelEquiv J f).val x = f (QuotientGroup.mk x) := by rfl

@[simp]
theorem quotientLevelEquiv_symm_apply_mk (J : Subgroup F) (f : level I M J) (x : F) :
    (quotientLevelEquiv J).symm f (QuotientGroup.mk x) = f.val x := by rfl

variable [TopologicalSpace F] [SeparatelyContinuousMul F] [Nonempty (CompactOpenSubgroup F)]

/-- The union of the algebras of smooth families fixed by a compact open subgroup.
Intersecting levels gives a common level for the sum or product. -/
def finiteLevel (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (F : Type*) [Group F] [TopologicalSpace F] [SeparatelyContinuousMul F]
    [Nonempty (CompactOpenSubgroup F)] :
    Subalgebra ℂ (F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) where
  carrier := {f | ∃ J : CompactOpenSubgroup F, f ∈ level I M J.toSubgroup}
  mul_mem' := by
    rintro _ _ ⟨J, hf⟩ ⟨K, hg⟩
    exact ⟨J ⊓ K, mul_mem (level_antitone (by exact inf_le_left) hf)
      (level_antitone (by exact inf_le_right) hg)⟩
  add_mem' := by
    rintro _ _ ⟨J, hf⟩ ⟨K, hg⟩
    exact ⟨J ⊓ K, add_mem (level_antitone (by exact inf_le_left) hf)
      (level_antitone (by exact inf_le_right) hg)⟩
  algebraMap_mem' z :=
    ⟨Classical.arbitrary (CompactOpenSubgroup F), Subalgebra.algebraMap_mem _ z⟩

/-- A smooth family belongs to the union exactly when one compact open subgroup fixes it. -/
theorem mem_finiteLevel_iff {f : F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} :
    f ∈ finiteLevel I M F ↔ ∃ J : CompactOpenSubgroup F, f ∈ level I M J.toSubgroup := by
  rfl

end AdelicSmoothFunction

/-- Complex-valued smooth functions of finite adelic level on `M × F`, as an algebra of
smooth families. Here `M` carries the archimedean manifold structure and `F` has a compact
open subgroup. -/
abbrev AdelicSmoothFunction (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] (F : Type*) [Group F] [TopologicalSpace F] [SeparatelyContinuousMul F]
    [Nonempty (CompactOpenSubgroup F)] :=
  ↥(AdelicSmoothFunction.finiteLevel I M F)

namespace AdelicSmoothFunction

variable [TopologicalSpace F] [SeparatelyContinuousMul F] [Nonempty (CompactOpenSubgroup F)]

/-- The smooth function of the archimedean variable obtained by fixing the finite variable. -/
def slice (f : AdelicSmoothFunction I M F) (x : F) : C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  f.val x

/-- Evaluate a function on the product of the archimedean and finite factors. -/
def eval (f : AdelicSmoothFunction I M F) (x : M × F) : ℂ :=
  f.slice x.2 x.1

@[simp]
theorem slice_apply (f : AdelicSmoothFunction I M F) (x : M × F) :
    f.slice x.2 x.1 = f.eval x := by rfl

@[ext]
theorem ext {f g : AdelicSmoothFunction I M F} (h : ∀ x, f.eval x = g.eval x) : f = g :=
  Subtype.ext (funext fun y ↦ ContMDiffMap.ext fun x ↦ h (x, y))

/-- Evaluation at a point is a homomorphism for the pointwise complex algebra. -/
def evalAlgHom (x : M × F) : AdelicSmoothFunction I M F →ₐ[ℂ] ℂ where
  toFun f := f.eval x
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' z := by
    simp [eval, slice, Pi.algebraMap_apply]

@[simp]
theorem evalAlgHom_apply (x : M × F) (f : AdelicSmoothFunction I M F) :
    evalAlgHom x f = f.eval x := by rfl

@[simp]
theorem eval_zero (x : M × F) : (0 : AdelicSmoothFunction I M F).eval x = 0 := by
  rw [← evalAlgHom_apply, map_zero]

@[simp]
theorem eval_one (x : M × F) : (1 : AdelicSmoothFunction I M F).eval x = 1 := by
  rw [← evalAlgHom_apply, map_one]

@[simp]
theorem eval_add (f g : AdelicSmoothFunction I M F) (x : M × F) :
    (f + g).eval x = f.eval x + g.eval x := by
  simpa only [evalAlgHom_apply] using map_add (evalAlgHom x) f g

@[simp]
theorem eval_mul (f g : AdelicSmoothFunction I M F) (x : M × F) :
    (f * g).eval x = f.eval x * g.eval x := by
  simpa only [evalAlgHom_apply] using map_mul (evalAlgHom x) f g

@[simp]
theorem eval_algebraMap (z : ℂ) (x : M × F) :
    (algebraMap ℂ (AdelicSmoothFunction I M F) z).eval x = z := by
  rw [← evalAlgHom_apply]
  exact (evalAlgHom (I := I) x).commutes z

@[simp]
theorem eval_smul (z : ℂ) (f : AdelicSmoothFunction I M F) (x : M × F) :
    (z • f).eval x = z * f.eval x := by
  rw [Algebra.smul_def, eval_mul, eval_algebraMap]

/-- Inclusion of the algebra of functions at a specified compact open level. -/
def ofLevel (J : CompactOpenSubgroup F) :
    level I M J.toSubgroup →ₐ[ℂ] AdelicSmoothFunction I M F :=
  Subalgebra.inclusion fun _ hf ↦ mem_finiteLevel_iff.mpr ⟨J, hf⟩

@[simp]
theorem ofLevel_slice (J : CompactOpenSubgroup F) (f : level I M J.toSubgroup) (x : F) :
    (ofLevel J f).slice x = f.val x := by rfl

/-- Inclusion at a smaller level uses the same function. -/
theorem ofLevel_inclusion {J K : CompactOpenSubgroup F} (h : K ≤ J)
    (f : level I M J.toSubgroup) :
    ofLevel K (Subalgebra.inclusion (level_antitone ((K.toSubgroup_le J).2 h)) f) =
      ofLevel J f := by rfl

/-- The image of a level inclusion consists of the functions fixed by that subgroup. -/
theorem mem_range_ofLevel_iff (J : CompactOpenSubgroup F) (f : AdelicSmoothFunction I M F) :
    f ∈ Set.range (ofLevel J) ↔ ∀ (x : F) (j : J.toSubgroup), f.slice (x * j) = f.slice x := by
  constructor
  · rintro ⟨a, rfl⟩
    simpa only [ofLevel_slice] using mem_level_iff.mp a.property
  · intro h
    exact ⟨⟨f.val, mem_level_iff.mpr h⟩, Subtype.ext rfl⟩

/-- Every function comes from a compact open level. -/
theorem exists_ofLevel
    (f : AdelicSmoothFunction I M F) :
    ∃ J : CompactOpenSubgroup F, f ∈ Set.range (ofLevel J) := by
  obtain ⟨J, hJ⟩ := mem_finiteLevel_iff.mp f.property
  exact ⟨J, ⟨⟨f.val, hJ⟩, Subtype.ext rfl⟩⟩

/-- Construct a finite-level function from its values on the product, smoothness of each
archimedean slice and right invariance at a specified compact open level. -/
def ofFun (f : M × F → ℂ) (J : CompactOpenSubgroup F)
    (hs : ∀ x : F, ContMDiff I 𝓘(ℝ, ℂ) ∞ fun m ↦ f (m, x))
    (hJ : ∀ (x : M × F) (j : J.toSubgroup), f (x.1, x.2 * j) = f x) :
    AdelicSmoothFunction I M F :=
  ofLevel J ⟨fun x ↦ ⟨fun m ↦ f (m, x), hs x⟩, mem_level_iff.mpr fun x j ↦
    ContMDiffMap.ext fun m ↦ hJ (m, x) j⟩

@[simp]
theorem eval_ofFun (f : M × F → ℂ) (J : CompactOpenSubgroup F)
    (hs : ∀ x : F, ContMDiff I 𝓘(ℝ, ℂ) ∞ fun m ↦ f (m, x))
    (hJ : ∀ (x : M × F) (j : J.toSubgroup), f (x.1, x.2 * j) = f x)
    (x : M × F) : (ofFun f J hs hJ).eval x = f x := by
  rfl

/-- Point evaluation is injective as a function of the full family of values. -/
theorem eval_injective : Function.Injective (eval : AdelicSmoothFunction I M F → M × F → ℂ) :=
  fun _ _ h ↦ ext (congrFun h)

/-- Level inclusion is injective. -/
theorem ofLevel_injective (J : CompactOpenSubgroup F) :
    Function.Injective (ofLevel (I := I) (M := M) J) :=
  Subalgebra.inclusion_injective _

/-- Finite level and smoothness of the slices imply joint continuity. -/
theorem continuous_eval
    (f : AdelicSmoothFunction I M F) : Continuous f.eval := by
  obtain ⟨J, a, rfl⟩ := f.exists_ofLevel
  let d := (quotientLevelEquiv J.toSubgroup).symm a
  have heval (x : M × F) :
      (ofLevel J a).eval x = d (QuotientGroup.mk x.2) x.1 := by
    simp only [d, eval, ofLevel_slice, quotientLevelEquiv_symm_apply_mk]
  let : DiscreteTopology (F ⧸ J.toSubgroup) := QuotientGroup.discreteTopology J.isOpen
  rw [funext heval]
  have hd : Continuous fun x : M × (F ⧸ J.toSubgroup) ↦ d x.2 x.1 :=
    continuous_prod_of_discrete_right.mpr fun q ↦ (d q).contMDiff.continuous
  exact hd.comp
    (continuous_fst.prodMk (QuotientGroup.continuous_mk.comp continuous_snd))

/-- Pull back the smooth slices along a smooth self-map and shift their finite indices. -/
private def translateSlices (a : C^∞⟮I, M; I, M⟯) (y : F) :
    (F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) →ₐ[ℂ] (F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) :=
  AlgHom.pi fun x ↦
    (ContMDiffMap.compRightComplexAlgHom a).comp (Pi.evalAlgHom ℂ _ (x * y))

omit [TopologicalSpace F] [SeparatelyContinuousMul F] in
private theorem translateSlices_apply (a : C^∞⟮I, M; I, M⟯) (y : F)
    (f : F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : F) :
    translateSlices a y f x = (f (x * y)).comp a := by
  simp [translateSlices, ContMDiffMap.compRightComplexAlgHom_apply]

omit [TopologicalSpace F] [SeparatelyContinuousMul F] in
private theorem translateSlices_eval (a : C^∞⟮I, M; I, M⟯) (y : F)
    (f : F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M × F) :
    translateSlices a y f x.2 x.1 = f (x.2 * y) (a x.1) := by
  rw [translateSlices_apply, ContMDiffMap.comp_apply]

omit [Nonempty (CompactOpenSubgroup F)] in
private theorem translateSlices_mem_level (a : C^∞⟮I, M; I, M⟯) (y : F) {J : CompactOpenSubgroup F}
    {f : F → C^∞⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯} (hf : f ∈ level I M J.toSubgroup) :
    translateSlices a y f ∈ level I M (ContinuousAut.conj y • J).toSubgroup := by
  refine mem_level_iff.mpr fun x j ↦ ?_
  have hj : y⁻¹ * (j : F) * y ∈ J :=
    ContinuousAut.mem_conj_smul_compactOpenSubgroup_iff.mp
      ((ContinuousAut.conj y • J).mem_toSubgroup.mp j.property)
  have h := mem_level_iff.mp hf (x * y) ⟨_, J.mem_toSubgroup.mpr hj⟩
  have he : x * (j : F) * y = (x * y) * (y⁻¹ * j * y) := by group
  rw [translateSlices_apply, translateSlices_apply, he, h]

/-- Pullback and finite index shift preserve the union of the compact open levels. -/
private def translateFiniteLevel (a : C^∞⟮I, M; I, M⟯) (y : F) :
    AdelicSmoothFunction I M F →ₐ[ℂ] AdelicSmoothFunction I M F :=
  ((translateSlices a y).comp (finiteLevel I M F).val).codRestrict _ fun f ↦ by
    obtain ⟨J, hJ⟩ := mem_finiteLevel_iff.mp f.property
    exact mem_finiteLevel_iff.mpr ⟨ContinuousAut.conj y • J, translateSlices_mem_level a y hJ⟩

private theorem translateFiniteLevel_eval (a : C^∞⟮I, M; I, M⟯) (y : F)
    (f : AdelicSmoothFunction I M F) (x : M × F) :
    (translateFiniteLevel a y f).eval x = f.eval (a x.1, x.2 * y) :=
  translateSlices_eval a y f.val x

section Translation

variable [Group M] [ContMDiffMul I ∞ M]

/-- Right translation of a family at level `J` has level `y_f J y_f⁻¹`. -/
def rightTranslateLevel (y : M × F) (J : CompactOpenSubgroup F) :
    level I M J.toSubgroup →ₐ[ℂ] level I M (ContinuousAut.conj y.2 • J).toSubgroup :=
  ((translateSlices (smoothRightMul I y.1) y.2).comp (level I M J.toSubgroup).val).codRestrict _
    fun f ↦ translateSlices_mem_level (smoothRightMul I y.1) y.2 f.property

omit [Nonempty (CompactOpenSubgroup F)] in
@[simp]
theorem rightTranslateLevel_apply (y : M × F) (J : CompactOpenSubgroup F)
    (f : level I M J.toSubgroup) (x : M × F) :
    (rightTranslateLevel y J f).val x.2 x.1 = f.val (x.2 * y.2) (x.1 * y.1) :=
  translateSlices_eval (smoothRightMul I y.1) y.2 f.val x

/-- Right translation `R(y)f(x) = f(xy)` as a complex algebra endomorphism. -/
def rightTranslate (y : M × F) :
    AdelicSmoothFunction I M F →ₐ[ℂ] AdelicSmoothFunction I M F :=
  translateFiniteLevel (smoothRightMul I y.1) y.2

@[simp]
theorem rightTranslate_eval (y : M × F) (f : AdelicSmoothFunction I M F) (x : M × F) :
    (rightTranslate y f).eval x = f.eval (x * y) :=
  translateFiniteLevel_eval (smoothRightMul I y.1) y.2 f x

/-- Translating after a level inclusion agrees with translating at the conjugate level. -/
theorem rightTranslate_ofLevel (y : M × F) (J : CompactOpenSubgroup F)
    (f : level I M J.toSubgroup) :
    rightTranslate y (ofLevel J f) =
      ofLevel (ContinuousAut.conj y.2 • J) (rightTranslateLevel y J f) := by
  ext x
  rw [rightTranslate_eval, eval, ofLevel_slice, eval, ofLevel_slice, rightTranslateLevel_apply]
  rfl

@[simp]
theorem rightTranslate_one :
    rightTranslate (I := I) (1 : M × F) = AlgHom.id ℂ (AdelicSmoothFunction I M F) := by
  apply AlgHom.ext
  intro f
  apply ext
  intro x
  simp

theorem rightTranslate_mul (y z : M × F) :
    rightTranslate (I := I) (y * z) = (rightTranslate y).comp (rightTranslate z) := by
  apply AlgHom.ext
  intro f
  apply ext
  intro x
  simp [mul_assoc]

/-- Right translations as a complex linear representation of the product group. -/
def rightTranslation : Representation ℂ (M × F) (AdelicSmoothFunction I M F) :=
  AlgHom.toEnd.comp
    { toFun := rightTranslate
      map_one' := rightTranslate_one
      map_mul' := rightTranslate_mul }

@[simp]
theorem rightTranslation_apply (y : M × F) (f : AdelicSmoothFunction I M F) (x : M × F) :
    (rightTranslation y f).eval x = f.eval (x * y) :=
  rightTranslate_eval y f x

end Translation

/-- The right action of the finite factor shifts the finite index of each smooth slice.
It is used to apply the smooth representation and Hecke algebra APIs. -/
def finiteRightTranslation : Representation ℂ F (AdelicSmoothFunction I M F) :=
  AlgHom.toEnd.comp
    { toFun := translateFiniteLevel (ContMDiffMap.id (I := I))
      map_one' := AlgHom.ext fun f ↦ ext fun x ↦ by
        rw [AlgHom.one_apply, translateFiniteLevel_eval]
        simp [ContMDiffMap.id]
      map_mul' y z := AlgHom.ext fun f ↦ ext fun x ↦ by
        simp only [AlgHom.mul_apply, translateFiniteLevel_eval]
        simp [ContMDiffMap.id, mul_assoc] }

@[simp]
theorem finiteRightTranslation_apply (y : F) (f : AdelicSmoothFunction I M F) (x : M × F) :
    (finiteRightTranslation y f).eval x = f.eval (x.1, x.2 * y) :=
  translateFiniteLevel_eval ContMDiffMap.id y f x

/-- The fixed vectors of the finite action at a compact open subgroup are exactly the
image of that level. -/
theorem mem_finiteRightTranslation_invariants_iff (J : CompactOpenSubgroup F)
    (f : AdelicSmoothFunction I M F) :
    f ∈ Representation.invariants
      ((finiteRightTranslation (I := I) (M := M)).comp J.toSubgroup.subtype) ↔
      f ∈ Set.range (ofLevel J) := by
  rw [Representation.mem_invariants, mem_range_ofLevel_iff]
  constructor
  · intro hf x j
    apply ContMDiffMap.ext
    intro m
    have hj := congrArg (fun a : AdelicSmoothFunction I M F ↦ a.eval (m, x)) (hf j)
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, finiteRightTranslation_apply] at hj
    exact hj
  · intro hf j
    apply ext
    intro x
    rw [MonoidHom.comp_apply, Subgroup.subtype_apply, finiteRightTranslation_apply]
    exact DFunLike.congr_fun (hf x.2 j) x.1

/-- The finite right-translation action is smooth because each function has a compact open
level fixing it. -/
instance : (finiteRightTranslation (I := I) (M := M) (F := F)).IsSmooth where
  isOpen_stabilizer f := by
    obtain ⟨J, hJ⟩ := f.exists_ofLevel
    refine Subgroup.isOpen_mono (H₁ := J.toSubgroup) (fun x hx ↦ ?_) J.isOpen
    have hf := (mem_finiteRightTranslation_invariants_iff J f).mpr hJ
    exact Representation.mem_stabilizer.mpr ((Representation.mem_invariants _ _).mp hf ⟨x, hx⟩)

/-- On a smooth group, finite right translation is the restriction of product right translation. -/
theorem finiteRightTranslation_eq_comp_inr [Group M] [ContMDiffMul I ∞ M] :
    finiteRightTranslation (I := I) (M := M) (F := F) =
      rightTranslation.comp (MonoidHom.inr M F) := by
  apply MonoidHom.ext
  intro y
  apply LinearMap.ext
  intro f
  apply ext
  intro x
  simp [Prod.mul_def]

section LeftInvariant

variable [Group M]

/-- The algebra of finite-level functions invariant by left translation by a subgroup `Γ`.
For adelic functions the rational diagonal supplies `Γ`. -/
def leftInvariant (Γ : Subgroup (M × F)) : Subalgebra ℂ (AdelicSmoothFunction I M F) where
  carrier := {f | ∀ (γ : Γ) (x : M × F), f.eval (γ * x) = f.eval x}
  mul_mem' hf hg γ x := by simp only [eval_mul, hf γ x, hg γ x]
  add_mem' hf hg γ x := by simp only [eval_add, hf γ x, hg γ x]
  algebraMap_mem' z γ x := by simp

@[simp]
theorem mem_leftInvariant_iff (Γ : Subgroup (M × F)) (f : AdelicSmoothFunction I M F) :
    f ∈ leftInvariant Γ ↔ ∀ (γ : Γ) (x : M × F), f.eval (γ * x) = f.eval x := by rfl

variable [ContMDiffMul I ∞ M]

/-- Right translation preserves left invariance. -/
theorem rightTranslate_mem_leftInvariant {Γ : Subgroup (M × F)}
    {f : AdelicSmoothFunction I M F} (hf : f ∈ leftInvariant Γ) (y : M × F) :
    rightTranslate y f ∈ leftInvariant Γ := by
  rw [mem_leftInvariant_iff] at hf ⊢
  intro γ x
  simpa only [rightTranslate_eval, mul_assoc] using hf γ (x * y)

/-- Right translation on functions invariant on the left by `Γ`. -/
def rightTranslateLeftInvariant (Γ : Subgroup (M × F)) (y : M × F) :
    leftInvariant (I := I) Γ →ₐ[ℂ] leftInvariant (I := I) Γ :=
  ((rightTranslate y).comp (leftInvariant Γ).val).codRestrict _
    fun f ↦ rightTranslate_mem_leftInvariant f.property y

@[simp]
theorem rightTranslateLeftInvariant_eval (Γ : Subgroup (M × F)) (y : M × F)
    (f : leftInvariant (I := I) Γ) (x : M × F) :
    (rightTranslateLeftInvariant Γ y f).val.eval x = f.val.eval (x * y) :=
  rightTranslate_eval y f.val x

end LeftInvariant

end AdelicSmoothFunction

end TauCeti
