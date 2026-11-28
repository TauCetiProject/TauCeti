/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.AlgebraicGeometry.GroupScheme.Torsor

/-!
# The kernel action of a group-scheme homomorphism

For a group-scheme homomorphism `f : G ⟶ H` over `S`, its kernel after base change to `H`
acts on `G` over `H` by left multiplication. The action is simply transitive on each fibre
on all test schemes. If `f` is flat, surjective and locally of finite presentation, then
`G ⟶ H` is an fppf torsor under this action. The kernel retains its scheme structure,
including when it is nonreduced.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.4.
* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Chapter I, §1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

open scoped MonObj

universe u

namespace TauCeti.GroupScheme

noncomputable section

variable {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)

private abbrev sourcePoint {T : Over H.X.left} (x : T ⟶ Over.mk f.hom.hom.left) :
    (Over.map H.X.hom).obj T ⟶ G.X :=
  Over.homMk x.left (by
    rw [← Over.w f.hom.hom, ← Category.assoc]
    exact congrArg (· ≫ H.X.hom) (Over.w x))

@[local simp]
private theorem sourcePoint_comp {T U : Over H.X.left} (t : U ⟶ T)
    (x : T ⟶ Over.mk f.hom.hom.left) :
    sourcePoint f (t ≫ x) = (Over.map H.X.hom).map t ≫ sourcePoint f x :=
  Over.OverMorphism.ext rfl

private theorem sourcePoint_injective (T : Over H.X.left) :
    Function.Injective (sourcePoint f (T := T)) :=
  fun _ _ h ↦ Over.OverMorphism.ext
    (congrArg (fun z : (Over.map H.X.hom).obj T ⟶ G.X ↦ z.left) h)

@[local simp]
private theorem sourcePoint_comp_hom {T : Over H.X.left} (x : T ⟶ Over.mk f.hom.hom.left) :
    sourcePoint f x ≫ f.hom.hom = Over.homMk T.hom rfl :=
  Over.OverMorphism.ext (Over.w x)

private def kernelPointMonoidHom (T : Over H.X.left) :
    (T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X) →*
      ((Over.map H.X.hom).obj T ⟶ G.X) :=
  (IsMonHom.monoidHom (kernel.ι f).hom.hom _).comp
    (baseChangePointMulEquiv H.X.hom (kernel f) T).toMonoidHom

private theorem kernelPointMonoidHom_apply {T : Over H.X.left}
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X) :
    kernelPointMonoidHom f T m =
      baseChangePointMulEquiv H.X.hom (kernel f) T m ≫ (kernel.ι f).hom.hom :=
  (rfl)

@[local simp]
private theorem kernelPointMonoidHom_comp {T U : Over H.X.left} (t : U ⟶ T)
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X) :
    kernelPointMonoidHom f U (t ≫ m) =
      (Over.map H.X.hom).map t ≫ kernelPointMonoidHom f T m := by
  simp only [kernelPointMonoidHom_apply, baseChangePointMulEquiv_naturality_left, Category.assoc]

@[local simp]
private theorem kernelPointMonoidHom_comp_hom {T : Over H.X.left}
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X) :
    kernelPointMonoidHom f T m ≫ f.hom.hom = 1 := by
  simp [kernelPointMonoidHom_apply]

@[instance_reducible]
private def kernelMulAction (T : Over H.X.left) :
    MulAction (T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X)
      ((yoneda.obj (Over.mk f.hom.hom.left)).obj (Opposite.op T)) where
  smul m x := Over.homMk (kernelPointMonoidHom f T m * sourcePoint f x).left (by
    have h : (kernelPointMonoidHom f T m * sourcePoint f x) ≫ f.hom.hom =
        Over.homMk T.hom rfl := by simp [MonObj.mul_comp]
    exact congrArg (fun z : (Over.map H.X.hom).obj T ⟶ H.X ↦ z.left) h)
  one_smul x := by
    refine Over.OverMorphism.ext (congrArg
      (fun z : (Over.map H.X.hom).obj T ⟶ G.X ↦ z.left)
      (?_ : kernelPointMonoidHom f T 1 * sourcePoint f x = sourcePoint f x))
    rw [map_one, one_mul]
  mul_smul m n x := by
    refine Over.OverMorphism.ext (congrArg
      (fun z : (Over.map H.X.hom).obj T ⟶ G.X ↦ z.left)
      (?_ : kernelPointMonoidHom f T (m * n) * sourcePoint f x =
        kernelPointMonoidHom f T m * (kernelPointMonoidHom f T n * sourcePoint f x)))
    rw [map_mul, mul_assoc]

attribute [local instance] kernelMulAction

private theorem sourcePoint_kernel_smul {T : Over H.X.left}
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X)
    (x : (yoneda.obj (Over.mk f.hom.hom.left)).obj (Opposite.op T)) :
    sourcePoint f (m • x) = kernelPointMonoidHom f T m * sourcePoint f x :=
  Over.OverMorphism.ext rfl

private theorem kernelMulAction_natural {T U : Over H.X.left} (t : U ⟶ T)
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X)
    (x : (yoneda.obj (Over.mk f.hom.hom.left)).obj (Opposite.op T)) :
    (yoneda.obj (Over.mk f.hom.hom.left)).map t.op (m • x) =
      (t ≫ m) • (yoneda.obj (Over.mk f.hom.hom.left)).map t.op x := by
  apply sourcePoint_injective f U
  rw [sourcePoint_kernel_smul]
  have h := sourcePoint_comp f t (m • x)
  rw [sourcePoint_kernel_smul, MonObj.comp_mul, ← kernelPointMonoidHom_comp,
    ← sourcePoint_comp] at h
  exact h

/-- The kernel of `f`, pulled back to the target, acts on the source over the target by
left multiplication. -/
@[instance_reducible]
def kernelAction :
    ModObj ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X (Over.mk f.hom.hom.left) :=
  TauCeti.ModObj.ofRepresentableBy _ (fun _ _ t m x ↦ kernelMulAction_natural f t m x)
    (Functor.RepresentableBy.yoneda _)

private theorem sourcePoint_kernelAction_smul {T : Over H.X.left}
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X)
    (x : T ⟶ Over.mk f.hom.hom.left) :
    let := kernelAction f
    sourcePoint f (m • x) = kernelPointMonoidHom f T m * sourcePoint f x := by
  let := kernelAction f
  have h := TauCeti.ModObj.homEquiv_smul_ofRepresentableBy
    (fun _ _ t m x ↦ kernelMulAction_natural f t m x) (Functor.RepresentableBy.yoneda _) m x
  simp only [Functor.RepresentableBy.coyoneda_homEquiv, Equiv.refl_apply] at h
  exact (congrArg (sourcePoint f) h).trans (sourcePoint_kernel_smul f m x)

/-- On test points the kernel action takes `(m, x)` to `m * x`, with the kernel point
viewed in the source group over the original base. -/
theorem kernelAction_smul_left {T : Over H.X.left}
    (m : T ⟶ ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X)
    (x : T ⟶ Over.mk f.hom.hom.left) :
    let := kernelAction f
    (m • x).left =
      ((baseChangePointMulEquiv H.X.hom (kernel f) T m ≫ (kernel.ι f).hom.hom) *
        (Over.homMk x.left (by
          rw [← Over.w f.hom.hom, ← Category.assoc]
          exact congrArg (· ≫ H.X.hom) (Over.w x)) :
          (Over.map H.X.hom).obj T ⟶ G.X)).left :=
  congrArg Over.Hom.left (sourcePoint_kernelAction_smul f m x)

/-- For the kernel action, the map `(m, x) ↦ (m • x, x)` from the product of the
base-changed kernel and the source to the fibre square of `f` is an isomorphism. -/
theorem isIso_leftSMul_kernelAction :
    let := kernelAction f
    IsIso (ModObj.leftSMul ((Over.pullback H.X.hom).mapGrp.obj (kernel f)).X
      (Over.mk f.hom.hom.left)) := by
  let := kernelAction f
  rw [ModObj.isIso_leftSMul_iff]
  intro T x y
  have hz : (sourcePoint f y * (sourcePoint f x)⁻¹) ≫ f.hom.hom = 1 := by
    simp [MonObj.mul_comp, GrpObj.inv_comp]
  let e := baseChangePointMulEquiv H.X.hom (kernel f) T
  let m := e.symm (kernelLift _ hz)
  have hm : kernelPointMonoidHom f T m = sourcePoint f y * (sourcePoint f x)⁻¹ := by
    rw [kernelPointMonoidHom_apply]
    exact (congrArg (· ≫ (kernel.ι f).hom.hom) (e.apply_symm_apply _)).trans (kernelLift_ι _ _)
  refine ⟨m, sourcePoint_injective f T ?_, fun n hn ↦ e.injective (kernel_hom_ext ?_)⟩
  · rw [sourcePoint_kernelAction_smul, hm, inv_mul_cancel_right]
  · have h := congrArg (sourcePoint f) hn
    rw [sourcePoint_kernelAction_smul] at h
    exact (eq_mul_inv_iff_mul_eq.mpr h).trans hm.symm

/-- A flat surjective homomorphism locally of finite presentation is an fppf torsor over
its target under its base-changed scheme-theoretic kernel. -/
theorem isTorsor_kernel [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    [LocallyOfFinitePresentation f.hom.hom.left] :
    let := kernelAction f
    (Scheme.fppfTopology.over H.X.left).IsTorsor
      ((Over.pullback H.X.hom).mapGrp.obj (kernel f)) (Over.mk f.hom.hom.left) := by
  let := kernelAction f
  have : Flat (Over.mk f.hom.hom.left).hom := ‹Flat f.hom.hom.left›
  have : Surjective (Over.mk f.hom.hom.left).hom := ‹Surjective f.hom.hom.left›
  have : LocallyOfFinitePresentation (Over.mk f.hom.hom.left).hom :=
    ‹LocallyOfFinitePresentation f.hom.hom.left›
  exact isTorsor_of_isIso_leftSMul (isIso_leftSMul_kernelAction f)

end

end TauCeti.GroupScheme
