/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Flat
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Connections compatible with a Clifford multiplication

Let `W` and `V` be vector bundles over `M`, with connections `∇ᵂ` and `∇`, and let
`c : W → End V` be a *Clifford multiplication*, a family of linear maps
`c x : W x → End (V x)`. In the geometric setting `W` is the tangent (or cotangent) bundle of a
Riemannian manifold with its Levi-Civita connection and `V` is a bundle of Clifford modules, but
no Clifford relation is needed here. The connection `∇` is **Clifford compatible at `x`**
(`CovariantDerivative.IsCliffordCompatibleAt`) if it satisfies the Leibniz rule

`∇_v (c(Y) s) = c(∇ᵂ_v Y) s + c(Y) ∇_v s`

for all tangent vectors `v` at `x` and all sections `Y` of `W` and `s` of `V` differentiable at
`x`, and **Clifford compatible** (`CovariantDerivative.IsCliffordCompatible`) if it is compatible
at every point. This file proves the basic structure theory of this condition.

* **Parallel multiplication.** Where `c` is differentiable, compatibility at a point is the
  vanishing there of the covariant derivative `∇c` of `c` as a section of `Hom(W, End V)`, for
  the connection induced by `∇ᵂ` and `∇`
  (`CovariantDerivative.isCliffordCompatibleAt_iff_hom_hom_eq_zero`). So for differentiable `c`,
  `∇` is compatible exactly when `c` is parallel
  (`CovariantDerivative.isCliffordCompatible_iff_hom_hom_eq_zero`).
* **Affine description.** If `∇` is compatible at `x`, then `∇ + A`, for a one-form `A` with
  values in `End V`, is compatible at `x` exactly when every `A(v)` at `x` commutes with every
  `c(w)` (`CovariantDerivative.IsCliffordCompatibleAt.isCliffordCompatibleAt_addOneForm_iff`, with
  the global form `CovariantDerivative.IsCliffordCompatible.isCliffordCompatible_addOneForm_iff`).
  Conversely, where `c` is differentiable, the difference tensor of two compatible connections
  commutes with `c` (`CovariantDerivative.IsCliffordCompatibleAt.difference_apply_comm`). Thus for
  differentiable `c` the compatible connections form an affine space over the one-forms with
  values in the commutant of `c`.
* **Curvature compatibility.** For smooth data the curvature of a compatible connection
  satisfies `R(u, v) (c(w) e) = c(Rᵂ(u, v) w) e + c(w) R(u, v) e`, that is
  `[R(u, v), c(w)] = c(Rᵂ(u, v) w)`
  (`CovariantDerivative.IsCliffordCompatible.curvatureTensor_leibniz`). This is the vanishing of
  the curvature of the induced connection on `Hom(W, End V)` on the parallel section `c`, read
  through `CovariantDerivative.curvatureTensor_hom_apply`.
* **Scalar multiplication.** Every connection is compatible with the multiplication of `V` by the
  trivial line, `c(a) = a • id`, for the canonical connection `d` of the trivial line
  (`CovariantDerivative.isCliffordCompatible_trivial_smulRight`); there the Leibniz rule is that
  of the connection itself.

Clifford compatibility with the Levi-Civita connection is the hypothesis under which the Dirac
operator `CovariantDerivative.diracOperator` of `(∇, c)` is the Dirac operator of a Clifford
module, and the curvature identity relates the curvature of `V` to the Riemann curvature in the
curvature term of the square of that operator.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §5 (Dirac bundles).
* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., World Scientific,
  Definition 12.1.64 and Lemma 12.1.31.
* N. Berline, E. Getzler, M. Vergne, *Heat Kernels and Dirac Operators*, Springer, 1992,
  Section 3.3 (Clifford connections).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [FiberBundle G W]
  (cov : CovariantDerivative I F V) (covW : CovariantDerivative I G W)
  (c : Π x : M, W x →L[𝕜] V x →L[𝕜] V x)

/-- A connection `∇` on `V` is **Clifford compatible at `x`** with a multiplication
`c : W → End V` and a connection `∇ᵂ` on `W` if it satisfies the Leibniz rule
`∇_v (c(Y) s) = c(∇ᵂ_v Y) s + c(Y) ∇_v s` for all tangent vectors `v` at `x` and all sections `Y`
and `s` differentiable at `x`. Where `c` is differentiable this says that the covariant
derivative of `c` as a section of `Hom(W, End V)` vanishes at `x`
(`CovariantDerivative.isCliffordCompatibleAt_iff_hom_hom_eq_zero`). -/
def IsCliffordCompatibleAt (x : M) : Prop :=
  ∀ ⦃Y : Π y : M, W y⦄ ⦃s : Π y : M, V y⦄, MDiffAt (T% Y) x → MDiffAt (T% s) x →
    ∀ v : TangentSpace I x,
      cov (fun y ↦ c y (Y y) (s y)) x v = c x (covW Y x v) (s x) + c x (Y x) (cov s x v)

/-- A connection `∇` on `V` is **Clifford compatible** with a multiplication `c : W → End V` and
a connection `∇ᵂ` on `W` if it is Clifford compatible at every point, that is if it satisfies the
Leibniz rule `∇_v (c(Y) s) = c(∇ᵂ_v Y) s + c(Y) ∇_v s` for all sections `Y` and `s`
differentiable at the base point of `v`. For differentiable `c` this says that `c` is parallel as
a section of `Hom(W, End V)` (`CovariantDerivative.isCliffordCompatible_iff_hom_hom_eq_zero`). -/
def IsCliffordCompatible : Prop :=
  ∀ x : M, cov.IsCliffordCompatibleAt covW c x

/-- Clifford compatibility at a point, in its defining form. -/
theorem isCliffordCompatibleAt_iff {x : M} :
    cov.IsCliffordCompatibleAt covW c x ↔
      ∀ ⦃Y : Π y : M, W y⦄ ⦃s : Π y : M, V y⦄, MDiffAt (T% Y) x → MDiffAt (T% s) x →
        ∀ v : TangentSpace I x,
          cov (fun y ↦ c y (Y y) (s y)) x v = c x (covW Y x v) (s x) + c x (Y x) (cov s x v) :=
  Iff.rfl

/-- Clifford compatibility is Clifford compatibility at every point. -/
theorem isCliffordCompatible_iff :
    cov.IsCliffordCompatible covW c ↔ ∀ x : M, cov.IsCliffordCompatibleAt covW c x :=
  Iff.rfl

/-- **Scalar multiplication is Clifford compatible.** Every connection `∇` on `V` is Clifford
compatible with the multiplication `c(a) = a • id` of `V` by the trivial line and the canonical
connection `d` of the trivial line: here the Leibniz rule is `∇_v (f s) = df(v) s + f ∇_v s`. -/
theorem isCliffordCompatible_trivial_smulRight :
    cov.IsCliffordCompatible (trivial 𝕜)
      (fun x ↦ (ContinuousLinearMap.id 𝕜 𝕜).smulRight (ContinuousLinearMap.id 𝕜 (V x))) := by
  intro x f s hf hs v
  rw [Trivial.mdifferentiableAt_section_iff] at hf
  have h := cov.covariantDerivative_smul_section_apply hf hs v
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_apply,
    trivial_apply]
  have hfs : (fun y ↦ f y • s y) = f • s := funext fun y ↦ (Pi.smul_apply' (i := y) ..).symm
  rw [hfs, h, add_comm]

variable {cov covW c}

/-- The Leibniz rule satisfied by a connection Clifford compatible at `x`. -/
theorem IsCliffordCompatibleAt.leibniz {x : M} (h : cov.IsCliffordCompatibleAt covW c x)
    {Y : Π y : M, W y} {s : Π y : M, V y} (hY : MDiffAt (T% Y) x) (hs : MDiffAt (T% s) x)
    (v : TangentSpace I x) :
    cov (fun y ↦ c y (Y y) (s y)) x v = c x (covW Y x v) (s x) + c x (Y x) (cov s x v) :=
  h hY hs v

/-- A Clifford compatible connection is Clifford compatible at every point. -/
theorem IsCliffordCompatible.isCliffordCompatibleAt (h : cov.IsCliffordCompatible covW c)
    (x : M) : cov.IsCliffordCompatibleAt covW c x :=
  h x

/-- The Leibniz rule satisfied by a Clifford compatible connection. -/
theorem IsCliffordCompatible.leibniz (h : cov.IsCliffordCompatible covW c) {x : M}
    {Y : Π y : M, W y} {s : Π y : M, V y} (hY : MDiffAt (T% Y) x) (hs : MDiffAt (T% s) x)
    (v : TangentSpace I x) :
    cov (fun y ↦ c y (Y y) (s y)) x v = c x (covW Y x v) (s x) + c x (Y x) (cov s x v) :=
  h x hY hs v

/-- **Changing a connection compatible at a point by a one-form.** If `∇` is Clifford compatible
at `x`, then `∇ + A`, for a one-form `A` with values in `End V`, is Clifford compatible at `x`
exactly when every `A(v)` at `x` commutes with every Clifford multiplication `c(w)`. -/
theorem IsCliffordCompatibleAt.isCliffordCompatibleAt_addOneForm_iff {x : M}
    (h : cov.IsCliffordCompatibleAt covW c x)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) :
    (cov.addOneForm A).IsCliffordCompatibleAt covW c x ↔
      ∀ (v : TangentSpace I x) (w : W x) (e : V x), A x (c x w e) v = c x w (A x e v) := by
  constructor
  · intro h' v w e
    have hY := mdifferentiableAt_extend I G w
    have hs := mdifferentiableAt_extend I F e
    have h₁ := h' hY hs v
    simp only [addOneForm_apply, add_apply, map_add] at h₁
    rw [h hY hs v] at h₁
    simp only [extend_apply_self] at h₁
    rw [← sub_eq_zero, ← sub_eq_zero.mpr h₁]
    abel
  · intro hA Y s hY hs v
    simp only [addOneForm_apply, add_apply, map_add, h hY hs v,
      hA v (Y x) (s x)]
    abel

/-- **Changing a compatible connection by a one-form.** If `∇` is Clifford compatible, then
`∇ + A`, for a one-form `A` with values in `End V`, is Clifford compatible exactly when every
`A(v)` commutes with every Clifford multiplication `c(w)`. -/
theorem IsCliffordCompatible.isCliffordCompatible_addOneForm_iff
    (h : cov.IsCliffordCompatible covW c)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) :
    (cov.addOneForm A).IsCliffordCompatible covW c ↔
      ∀ (x : M) (v : TangentSpace I x) (w : W x) (e : V x), A x (c x w e) v = c x w (A x e v) :=
  forall_congr' fun x ↦ (h x).isCliffordCompatibleAt_addOneForm_iff A

variable [CompleteSpace 𝕜] [VectorBundle 𝕜 F V] [VectorBundle 𝕜 G W] [FiniteDimensional 𝕜 F]
  [ContMDiffVectorBundle 1 F V I]

/-- **Two compatible connections differ by a one-form commuting with the multiplication.** If
`∇` and `∇'` are both Clifford compatible at `x` and `c` is differentiable at `x`, then their
difference tensor at `x` commutes with every Clifford multiplication `c(w)`. -/
theorem IsCliffordCompatibleAt.difference_apply_comm {cov' : CovariantDerivative I F V} {x : M}
    (h : cov.IsCliffordCompatibleAt covW c x) (h' : cov'.IsCliffordCompatibleAt covW c x)
    (hc : MDiffAt (fun y ↦ TotalSpace.mk' (G →L[𝕜] F →L[𝕜] F)
      (E := fun z ↦ W z →L[𝕜] V z →L[𝕜] V z) y (c y)) x)
    (v : TangentSpace I x) (w : W x) (e : V x) :
    cov'.difference cov x (c x w e) v = c x w (cov'.difference cov x e v) := by
  have hY := mdifferentiableAt_extend I G w
  have hs := mdifferentiableAt_extend I F e
  have hcs := (hc.clm_bundle_apply hY).clm_bundle_apply hs
  have h₁ := cov'.difference_apply cov hcs
  have h₂ := cov'.difference_apply cov hs
  simp only [extend_apply_self] at h₁ h₂
  rw [h₁, h₂, sub_apply, sub_apply, h' hY hs v, h hY hs v, map_sub]
  simp only [extend_apply_self]
  abel

variable [FiniteDimensional 𝕜 G] [IsManifold I 1 M] [ContMDiffVectorBundle 1 G W I]

variable (cov covW c) in
/-- **Clifford compatibility at a point is parallelism of the multiplication.** Where `c` is
differentiable, the covariant derivative of `c` as a section of `Hom(W, End V)` vanishes at `x`
exactly when the Leibniz rule `∇_v (c(Y) s) = c(∇ᵂ_v Y) s + c(Y) ∇_v s` holds at `x` for all
sections `Y` and `s` differentiable at `x`. -/
theorem isCliffordCompatibleAt_iff_hom_hom_eq_zero {x : M}
    (hc : MDiffAt (fun y ↦ TotalSpace.mk' (G →L[𝕜] F →L[𝕜] F)
      (E := fun z ↦ W z →L[𝕜] V z →L[𝕜] V z) y (c y)) x) :
    cov.IsCliffordCompatibleAt covW c x ↔ covW.hom (cov.hom cov) c x = 0 := by
  constructor
  · intro h
    ext v w e
    have hcY := hom_hom_apply covW cov cov hc (mdifferentiableAt_extend I G w)
      (mdifferentiableAt_extend I F e) v
    simp only [extend_apply_self] at hcY
    rw [hcY, h (mdifferentiableAt_extend I G w) (mdifferentiableAt_extend I F e),
      extend_apply_self, extend_apply_self]
    simp
  · intro h Y s hY hs v
    have hcY := hom_hom_apply covW cov cov hc hY hs v
    rw [h] at hcY
    simp only [zero_apply] at hcY
    rw [eq_comm, sub_sub, sub_eq_zero] at hcY
    exact hcY

/-- **Clifford compatibility is parallelism of the multiplication.** For a multiplication `c`
differentiable as a section of `Hom(W, End V)`, the connection `∇` is Clifford compatible exactly
when `c` is parallel for the connection induced by `∇ᵂ` and `∇`. -/
theorem isCliffordCompatible_iff_hom_hom_eq_zero
    (hc : ∀ x, MDiffAt (fun y ↦ TotalSpace.mk' (G →L[𝕜] F →L[𝕜] F)
      (E := fun z ↦ W z →L[𝕜] V z →L[𝕜] V z) y (c y)) x) :
    cov.IsCliffordCompatible covW c ↔ ∀ x, covW.hom (cov.hom cov) c x = 0 :=
  forall_congr' fun x ↦ isCliffordCompatibleAt_iff_hom_hom_eq_zero cov covW c (hc x)

end General

section Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]
  {cov : CovariantDerivative I F V} {covW : CovariantDerivative I G W}
  [ContMDiffCovariantDerivative cov ∞] [ContMDiffCovariantDerivative covW ∞]
  {c : Π x : M, W x →L[ℝ] V x →L[ℝ] V x}

/-- **Curvature compatibility.** The curvature of a connection compatible with a smooth Clifford
multiplication `c` acts on `c` as a derivation:
`R(u, v) (c(w) e) = c(Rᵂ(u, v) w) e + c(w) R(u, v) e`. Equivalently, the commutator
`[R(u, v), c(w)]` is the Clifford multiplication by `Rᵂ(u, v) w`. -/
theorem IsCliffordCompatible.curvatureTensor_leibniz (h : cov.IsCliffordCompatible covW c)
    (hc : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F →L[ℝ] F)) ∞ (fun y ↦ TotalSpace.mk'
      (G →L[ℝ] F →L[ℝ] F) (E := fun z ↦ W z →L[ℝ] V z →L[ℝ] V z) y (c y)))
    (x : M) (u v : TangentSpace I x) (w : W x) (e : V x) :
    cov.curvatureTensor x u v (c x w e) =
      c x (covW.curvatureTensor x u v w) e + c x w (cov.curvatureTensor x u v e) := by
  have hpar :=
    (isCliffordCompatible_iff_hom_hom_eq_zero fun y ↦ (hc y).mdifferentiableAt (by simp)).1 h
  have h₀ := (covW.hom (cov.hom cov)).curvatureTensor_apply_eq_zero_of_cov_eq_zero
    isOpen_univ (Set.mem_univ x) hc.contMDiffOn (fun y _ ↦ hpar y) u v
  have h₁ := congr($h₀ w e)
  rw [curvatureTensor_hom_apply, sub_apply,
    curvatureTensor_hom_apply] at h₁
  simp only [zero_apply, sub_sub, sub_eq_zero] at h₁
  rw [h₁, add_comm]

end Curvature

end CovariantDerivative
