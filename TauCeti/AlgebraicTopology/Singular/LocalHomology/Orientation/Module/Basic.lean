/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
public import TauCeti.Algebra.Group.Units.ULift
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.OpenEmbedding
public import TauCeti.Data.ZMod.RingHoms
import TauCeti.Geometry.Manifold.ModelTransport.Finrank
/-!
# Module orientations of manifolds

For Hausdorff `M` modelled on a finite-dimensional real normed space `E`, ring `R`, and `R`-module
`N`, a *local `N`-orientation* at `x` (`ModuleLocalOrientation N M x d`) generates
`H_d(M, M ∖ {x}; N)`, and an *`N`-orientation* (`ModuleOrientation N M E d`) is a
transport-invariant choice at each `x`. Feeds `Orientation.{Basic,Transport,Homological}`
and `Orientation.OpenEmbedding` (where `ULift ℤ` specializes to `HomologicalOrientation`) and
`Orientation.Module.FundamentalClass` (relative/global fundamental classes for closed-manifold
Poincaré duality over arbitrary rings); for `N = R`, `d = finrank ℝ E`, this is Hatcher's
*`R`-orientation* (§3.3):
* `[IsDedekindFiniteMonoid R]`: local `N`-orientations in a fibre `≃ₗ[R] R` match `Rˣ`
  (`equivUnits`); `Rˣ` acts pretransitively (transitive when `R`-orientable) on `R`-orientations of
  a connected `n`-manifold (`exists_units_smul_eq`).
* `[CommRing R]`, `[FaithfulSMul R N]`: `Rˣ` acts freely on nonempty `n`-manifolds
  (`units_smul_injective`).
* Dedekind-finite `K`, `[Subsingleton Kˣ]`: unique `K`-orientation (`uniqueOfSubsingletonUnits`).
* `[CommRing R]`, `(2 : R) = 0`: exact scalar extension (`extendScalars`, via `extendScalarsObj`)
  along `ZMod.castULiftHom` from `ULift (ZMod 2)` yields `ofTwoEqZero`.
Ref: A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §3.3. -/
public noncomputable section
open CategoryTheory Limits Module Topology
open CategoryTheory.ConcreteCategory (congr_hom)
open CategoryTheory.Functor.Monoidal (εIso)
open ModuleCat (of span_singleton_apply_eq_top_iff)
open ModuleCat.ExtendScalars (apply_tmul_of_comm span_singleton_one_tmul_eq_top)
open scoped ChangeOfRings
universe w v u
namespace TauCeti
section Local
variable {M : Type w} [TopologicalSpace M]
  {R : Type u} [Ring R] (N : ModuleCat.{w} R)
/-- `z ∈ H_d(M, M ∖ {x}; N)` is a *local `N`-orientation* when it generates that `R`-module. -/
def IsModuleLocalOrientation (x : M) (d : ℕ) (z : ↑(localHomology N {x} d)) : Prop :=
  Submodule.span R {z} = ⊤
theorem isModuleLocalOrientation_iff (x : M) (d : ℕ) (z : ↑(localHomology N {x} d)) :
    IsModuleLocalOrientation N x d z ↔ Submodule.span R {z} = ⊤ := Iff.rfl
/-- The subtype of local `N`-orientations inside `H_d(M, M ∖ {x}; N)`. -/
abbrev ModuleLocalOrientation (M : Type w) [TopologicalSpace M] (x : M) (d : ℕ) :=
  {z : ↑(localHomology N {x} d) // IsModuleLocalOrientation N x d z}
variable {N} {x : M} {d : ℕ}
theorem isModuleLocalOrientation_smul_iff_of_isUnit {r : R} (hr : IsUnit r)
    {z : ↑(localHomology N {x} d)} :
    IsModuleLocalOrientation N x d (r • z) ↔ IsModuleLocalOrientation N x d z := by
  simp only [isModuleLocalOrientation_iff, Submodule.span_singleton_smul_eq hr]
@[simp] theorem isModuleLocalOrientation_neg_iff {z : ↑(localHomology N {x} d)} :
    IsModuleLocalOrientation N x d (-z) ↔ IsModuleLocalOrientation N x d z := by
  rw [← neg_one_smul R z]; exact isModuleLocalOrientation_smul_iff_of_isUnit isUnit_one.neg
theorem IsModuleLocalOrientation.neg {z : ↑(localHomology N {x} d)}
    (hz : IsModuleLocalOrientation N x d z) : IsModuleLocalOrientation N x d (-z) :=
  isModuleLocalOrientation_neg_iff.2 hz
instance : MulAction Rˣ (ModuleLocalOrientation N M x d) where
  smul u z := ⟨(u : R) • z.val, (isModuleLocalOrientation_smul_iff_of_isUnit u.isUnit).2 z.property⟩
  one_smul z := Subtype.ext (one_smul R z.val)
  mul_smul u v z := Subtype.ext (mul_smul (u : R) (v : R) z.val)
instance : InvolutiveNeg (ModuleLocalOrientation N M x d) :=
  { neg := fun z ↦ ⟨-z.val, z.property.neg⟩, neg_neg := fun z ↦ Subtype.ext (neg_neg z.val) }
namespace ModuleLocalOrientation
@[simp] lemma coe_smul (u : Rˣ) (z : ModuleLocalOrientation N M x d) :
    (u • z).val = (u : R) • z.val := (rfl)
@[simp] lemma coe_neg (z : ModuleLocalOrientation N M x d) : (-z).val = -z.val := (rfl)
/-- An iso `e : N ≅ N'` identifies local `N`-orientations with local `N'`-orientations. -/
def equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N') (x : M) (d : ℕ) :
    ModuleLocalOrientation N M x d ≃ ModuleLocalOrientation N' M x d :=
  let iso := localHomologyIsoOfCoefficientsIso e {x} d
  iso.toLinearEquiv.toEquiv.subtypeEquiv fun _ ↦ (span_singleton_apply_eq_top_iff iso.hom).symm
section
variable {N' : ModuleCat.{w} R} (e : N ≅ N') (x : M) (d : ℕ)
@[simp] lemma coe_equivOfCoefficientsIso (z : ModuleLocalOrientation N M x d) :
    (equivOfCoefficientsIso e x d z).val =
      (localHomologyIsoOfCoefficientsIso e {x} d).hom z.val := (rfl)
@[simp] lemma coe_equivOfCoefficientsIso_symm (z : ModuleLocalOrientation N' M x d) :
    ((equivOfCoefficientsIso e x d).symm z).val =
      (localHomologyIsoOfCoefficientsIso e {x} d).inv z.val := (rfl)
@[simp] lemma equivOfCoefficientsIso_smul (u : Rˣ) (z : ModuleLocalOrientation N M x d) :
    equivOfCoefficientsIso e x d (u • z) = u • equivOfCoefficientsIso e x d z :=
  Subtype.ext (map_smul (localHomologyIsoOfCoefficientsIso e {x} d).hom.hom (u : R) z.val)
@[simp] lemma equivOfCoefficientsIso_neg (z : ModuleLocalOrientation N M x d) :
    equivOfCoefficientsIso e x d (-z) = -equivOfCoefficientsIso e x d z :=
  Subtype.ext (map_neg (localHomologyIsoOfCoefficientsIso e {x} d).hom.hom z.val)
end
end ModuleLocalOrientation
end Local
section BaseRing
section
variable {M : Type w} [TopologicalSpace M] {R : Type u} [Ring R] {N : ModuleCat.{w} R}
  {x : M} {d : ℕ} (e : ↑(localHomology N {x} d) ≃ₗ[R] R)
/-- Under `H_d(M, M ∖ {x}; N) ≃ₗ[R] R`, the preimage of `1` is a local `N`-orientation. -/
theorem isModuleLocalOrientation_inv_one : IsModuleLocalOrientation N x d (e.symm 1) :=
  e.symm.span_singleton_apply_eq_top_iff.2
    ((Ideal.eq_top_iff_one _).2 (Submodule.mem_span_singleton_self 1))
variable [IsDedekindFiniteMonoid R]
namespace ModuleLocalOrientation
/-- Over a Dedekind-finite ring, `e : H_d ≃ₗ[R] R` identifies local orientations with `Rˣ`. -/
def equivUnits : ModuleLocalOrientation N M x d ≃ Rˣ :=
  ⟨fun z ↦ (e.span_singleton_eq_top_iff_isUnit.1 z.property).unit,
   fun u ↦ u • ⟨e.symm 1, isModuleLocalOrientation_inv_one e⟩,
   fun z ↦ Subtype.ext <| by rw [coe_smul, IsUnit.unit_spec, ← map_smul, smul_eq_mul, mul_one,
     e.symm_apply_apply], fun u ↦ Units.ext <| (IsUnit.unit_spec _).trans <| by
     rw [coe_smul, map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]⟩
@[simp] lemma coe_equivUnits_apply (z : ModuleLocalOrientation N M x d) :
    ((equivUnits e z : Rˣ) : R) = e z.val := IsUnit.unit_spec _
@[simp] lemma coe_equivUnits_symm_apply (u : Rˣ) : ((equivUnits e).symm u).val = e.symm (u : R) :=
  (map_smul e.symm (u : R) 1).symm.trans (congrArg e.symm (mul_one _))
@[simp] lemma equivUnits_smul (u : Rˣ) (z : ModuleLocalOrientation N M x d) :
    equivUnits e (u • z) = u * equivUnits e z := Units.ext <| by simp [smul_eq_mul]
@[simp] lemma equivUnits_neg (z : ModuleLocalOrientation N M x d) :
    equivUnits e (-z) = -equivUnits e z := Units.ext <| by simp
end ModuleLocalOrientation
end
section Chart
variable {M E : Type w} [TopologicalSpace M] [T1Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {R : Type w} [Ring R] (φ : OpenPartialHomeomorph M E) {x : M}
  (hx : x ∈ φ.source)
/-- The local `R`-orientation at `x` selected by a chart `φ` to `E`, for `n = finrank ℝ E`. -/
def moduleLocalOrientationOfChart {n : ℕ} (hn : finrank ℝ E = n) :
    ModuleLocalOrientation (of R R) M x n :=
  hn ▸ ⟨(singularHomologyComplSingletonFinrankIso (of R R) φ hx).inv (1 : R),
    isModuleLocalOrientation_inv_one
      (singularHomologyComplSingletonFinrankIso (of R R) φ hx).toLinearEquiv⟩
@[simp] lemma coe_moduleLocalOrientationOfChart :
    (moduleLocalOrientationOfChart (R := R) φ hx rfl).val =
      (singularHomologyComplSingletonFinrankIso (of R R) φ hx).inv (1 : R) := (rfl)
lemma singularHomologyComplSingletonFinrankIso_moduleLocalOrientationOfChart :
    (singularHomologyComplSingletonFinrankIso (of R R) φ hx).hom
      (moduleLocalOrientationOfChart (R := R) φ hx rfl).val = (1 : R) :=
  (singularHomologyComplSingletonFinrankIso (of R R) φ hx).inv_hom_id_apply 1
end Chart
namespace ModuleLocalOrientation
variable {M : Type w} {E : Type v} [TopologicalSpace M] [T1Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
/-- Every point of a `T₁` `n`-manifold has a local `R`-orientation in degree `n`. -/
theorem nonempty_of_finrank_eq {R : Type w} [Ring R] (x : M) {n : ℕ} (hn : finrank ℝ E = n) :
    Nonempty (ModuleLocalOrientation (of R R) M x n) :=
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  let _ : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  ⟨moduleLocalOrientationOfChart (chartAt E' x) (mem_chart_source E' x) (by simpa [E'] using hn)⟩
/-- At a point of an `n`-manifold (`[CommRing R]`, faithful `N`), `Rˣ` acts freely. -/
theorem units_smul_injective {R : Type u} [CommRing R] {N : ModuleCat.{w} R} [FaithfulSMul R N]
    {x : M} {n : ℕ} (hn : finrank ℝ E = n) (z : ModuleLocalOrientation N M x n) :
    Function.Injective fun u : Rˣ ↦ u • z := by
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  let _ : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  have hE' : finrank ℝ E' = n := by simpa [E'] using hn
  subst hE'; intro u v huv
  have hfix : ((u⁻¹ * v : Rˣ) : R) • z.val = z.val := (mul_smul _ _ _).trans
    ((congrArg ((u⁻¹ : Rˣ) • ·) (congrArg Subtype.val huv).symm).trans (inv_smul_smul u z.val))
  exact inv_mul_eq_one.1 <| Units.ext <| (singularHomologyComplSingletonFinrankIso N (chartAt E' x)
    (mem_chart_source E' x)).toLinearEquiv.eq_one_of_smul_eq_self_of_span_singleton_eq_top
      z.property hfix
/-- Unique local `K`-orientation at `x` for Dedekind-finite `K` with `[Subsingleton Kˣ]`. -/
@[instance_reducible] def uniqueOfSubsingletonUnits {K : Type w} [Ring K] [IsDedekindFiniteMonoid K]
    [Subsingleton Kˣ] (x : M) {n : ℕ} (hn : finrank ℝ E = n) :
    Unique (ModuleLocalOrientation (of K K) M x n) :=
  let E' := ULift.{w} (Fin (finrank ℝ E)) → ℝ
  letI : ChartedSpace E' M := ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := E) M (by simp [E'])
  have hE' : finrank ℝ E' = n := by simpa [E'] using hn
  ⟨⟨moduleLocalOrientationOfChart (chartAt E' x) (mem_chart_source E' x) hE'⟩, fun z ↦ by
    subst hE'
    exact (equivUnits (singularHomologyComplSingletonFinrankIso (of K K) (chartAt E' x)
      (mem_chart_source E' x)).toLinearEquiv).injective (Subsingleton.elim _ _)⟩
end ModuleLocalOrientation
end BaseRing
section Transport
variable {R : Type u} [Ring R] (N : ModuleCat.{w} R) (M E : Type w) [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M] (d : ℕ)
/-- Transport of local `N`-orientations along a path class via `localHomologyTransport`. -/
def moduleLocalOrientationTransport {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    ModuleLocalOrientation N M x.as d ≃ ModuleLocalOrientation N M y.as d :=
  let e := (localHomologySystem N M E d).mapIso (asIso f)
  e.toLinearEquiv.toEquiv.subtypeEquiv fun _ ↦ (span_singleton_apply_eq_top_iff e.hom).symm
section
variable {x y : FundamentalGroupoid M} (f : x ⟶ y)
@[simp] lemma coe_moduleLocalOrientationTransport (z : ModuleLocalOrientation N M x.as d) :
    (moduleLocalOrientationTransport N M E d f z).val = localHomologyTransport N M E d f z.val :=
  (rfl)
@[simp] lemma coe_moduleLocalOrientationTransport_symm (z : ModuleLocalOrientation N M y.as d) :
    ((moduleLocalOrientationTransport N M E d f).symm z).val =
      localHomologyTransport N M E d (inv f) z.val := (rfl)
@[simp] lemma moduleLocalOrientationTransport_inv : moduleLocalOrientationTransport N M E d (inv f)
    = (moduleLocalOrientationTransport N M E d f).symm := Equiv.ext fun _ ↦ Subtype.ext (by simp)
@[simp] lemma moduleLocalOrientationTransport_smul (u : Rˣ)
    (z : ModuleLocalOrientation N M x.as d) : moduleLocalOrientationTransport N M E d f (u • z) =
      u • moduleLocalOrientationTransport N M E d f z :=
  Subtype.ext (map_smul (localHomologyTransport N M E d f).hom (u : R) z.val)
@[simp] lemma moduleLocalOrientationTransport_neg (z : ModuleLocalOrientation N M x.as d) :
    moduleLocalOrientationTransport N M E d f (-z) = -moduleLocalOrientationTransport N M E d f z :=
  Subtype.ext (map_neg (localHomologyTransport N M E d f).hom z.val)
end
@[simp] lemma moduleLocalOrientationTransport_id (x : FundamentalGroupoid M) :
    moduleLocalOrientationTransport N M E d (𝟙 x) = Equiv.refl _ :=
  Equiv.ext fun _ ↦ Subtype.ext (by simp)
@[simp] lemma moduleLocalOrientationTransport_comp {x y z : FundamentalGroupoid M} (f : x ⟶ y)
    (g : y ⟶ z) : moduleLocalOrientationTransport N M E d (f ≫ g) =
      (moduleLocalOrientationTransport N M E d f).trans
        (moduleLocalOrientationTransport N M E d g) :=
  Equiv.ext fun _ ↦ Subtype.ext (by simp [localHomologyTransport_comp])
end Transport
end TauCeti
namespace Topology.IsOpenEmbedding
open TauCeti
variable {M M' : Type w} [TopologicalSpace M] [TopologicalSpace M'] [T1Space M'] {j : M → M'}
  {R : Type u} [Ring R]
/-- Open embedding `j : M → M'` (`T₁` target) identifies local `N`-orientations via excision. -/
def moduleLocalOrientationEquiv (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M) (d : ℕ) :
    ModuleLocalOrientation N M x d ≃ ModuleLocalOrientation N M' (j x) d :=
  let e := localHomologyIsoOfIsOpenEmbedding N hj x d
  e.toLinearEquiv.toEquiv.subtypeEquiv fun _ ↦ (span_singleton_apply_eq_top_iff e.hom).symm
section
variable (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M) {d : ℕ}
@[simp] lemma coe_moduleLocalOrientationEquiv (z : ModuleLocalOrientation N M x d) :
    (hj.moduleLocalOrientationEquiv N x d z).val =
      (localHomologyIsoOfIsOpenEmbedding N hj x d).hom z.val := (rfl)
@[simp] lemma coe_moduleLocalOrientationEquiv_symm (z : ModuleLocalOrientation N M' (j x) d) :
    ((hj.moduleLocalOrientationEquiv N x d).symm z).val =
      (localHomologyIsoOfIsOpenEmbedding N hj x d).inv z.val := (rfl)
lemma localHomologyMap_moduleLocalOrientationEquiv_symm (z : ModuleLocalOrientation N M' (j x) d)
    (h : j ⁻¹' {j x} ⊆ {x}) : localHomologyMap N ⟨j, hj.continuous⟩ h d
      ((hj.moduleLocalOrientationEquiv N x d).symm z).val = z.val := by
  have h' := (localHomologyIsoOfIsOpenEmbedding N hj x d).inv_hom_id_apply z.val
  rwa [localHomologyIsoOfIsOpenEmbedding_hom, ← coe_moduleLocalOrientationEquiv_symm] at h'
@[simp] lemma moduleLocalOrientationEquiv_smul (u : Rˣ) (z : ModuleLocalOrientation N M x d) :
    hj.moduleLocalOrientationEquiv N x d (u • z) = u • hj.moduleLocalOrientationEquiv N x d z :=
  Subtype.ext (map_smul (localHomologyIsoOfIsOpenEmbedding N hj x d).hom.hom (u : R) z.val)
@[simp] lemma moduleLocalOrientationEquiv_neg (z : ModuleLocalOrientation N M x d) :
    hj.moduleLocalOrientationEquiv N x d (-z) = -hj.moduleLocalOrientationEquiv N x d z :=
  Subtype.ext (map_neg (localHomologyIsoOfIsOpenEmbedding N hj x d).hom.hom z.val)
end
@[simp] lemma moduleLocalOrientationEquiv_id [T1Space M] (N : ModuleCat.{w} R) (x : M) (d : ℕ) :
    IsOpenEmbedding.id.moduleLocalOrientationEquiv N x d = Equiv.refl _ :=
  Equiv.ext fun _ ↦ Subtype.ext (by simp [localHomologyIsoOfIsOpenEmbedding_id])
@[simp] lemma moduleLocalOrientationEquiv_trans {M'' : Type w} [TopologicalSpace M''] [T1Space M'']
    {j' : M' → M''} (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (N : ModuleCat.{w} R)
    (x : M) (d : ℕ) : (hj.moduleLocalOrientationEquiv N x d).trans
      (hj'.moduleLocalOrientationEquiv N (j x) d) =
      (hj'.comp hj).moduleLocalOrientationEquiv N x d := Equiv.ext fun _ ↦ Subtype.ext <| by
  rw [Equiv.trans_apply, coe_moduleLocalOrientationEquiv, coe_moduleLocalOrientationEquiv,
    coe_moduleLocalOrientationEquiv, ← comp_apply, ← Iso.trans_hom,
    localHomologyIsoOfIsOpenEmbedding_trans]
end Topology.IsOpenEmbedding
namespace TauCeti
section LocalExtendScalars
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{w} f)] {M : Type w} [TopologicalSpace M]
  {x : M} {d : ℕ}
/-- Exact scalar extension along `f : R →+* S` preserves local `N`-orientations. -/
theorem IsModuleLocalOrientation.extendScalarsObj {N : ModuleCat.{w} R}
    {z : ↑(localHomology N {x} d)} (hz : IsModuleLocalOrientation N x d z) :
    IsModuleLocalOrientation ((ModuleCat.extendScalars.{w} f).obj N) x d
      ((localHomologyObjIso (ModuleCat.extendScalars.{w} f) N {x} d).hom ((1 : S) ⊗ₜ[R, f] z)) :=
  (span_singleton_apply_eq_top_iff _).2 (span_singleton_one_tmul_eq_top f hz)
/-- Exact scalar extension along `f : R →+* S` sends local `R`-orientations to `S`-orientations. -/
theorem IsModuleLocalOrientation.extendScalars {z : ↑(localHomology (of R R) {x} d)}
    (hz : IsModuleLocalOrientation (of R R) x d z) : IsModuleLocalOrientation (of S S) x d
      ((localHomologyExtendScalarsIso f {x} d).hom ((1 : S) ⊗ₜ[R, f] z)) :=
  ((congr_hom (localHomologyExtendScalarsIso_hom f {x} d) ((1 : S) ⊗ₜ[R, f] z)).trans
    (comp_apply _ _ _)) ▸ (span_singleton_apply_eq_top_iff _).2 (hz.extendScalarsObj f)
namespace ModuleLocalOrientation
variable {N : ModuleCat.{w} R}
/-- Exact extension of scalars along `f : R →+* S` on local `N`-orientations for arbitrary `N`. -/
def extendScalarsObj (z : ModuleLocalOrientation N M x d) :
    ModuleLocalOrientation ((ModuleCat.extendScalars.{w} f).obj N) M x d :=
  ⟨(localHomologyObjIso (ModuleCat.extendScalars.{w} f) N {x} d).hom ((1 : S) ⊗ₜ[R, f] z.val),
    z.property.extendScalarsObj f⟩
@[simp] lemma coe_extendScalarsObj (z : ModuleLocalOrientation N M x d) :
    (z.extendScalarsObj f).val = (localHomologyObjIso (ModuleCat.extendScalars.{w} f) N {x} d).hom
      ((1 : S) ⊗ₜ[R, f] z.val) := (rfl)
@[simp] lemma extendScalarsObj_smul (u : Rˣ) (z : ModuleLocalOrientation N M x d) :
    (u • z).extendScalarsObj f = Units.map f.toMonoidHom u • z.extendScalarsObj f :=
  Subtype.ext <| by
    have hcomm : (ModuleCat.extendScalars.{w} f).map ((u : R) • 𝟙 _) ≫
        (localHomologyObjIso (ModuleCat.extendScalars.{w} f) N {x} d).hom =
        (localHomologyObjIso (ModuleCat.extendScalars.{w} f) N {x} d).hom ≫ ((f u : S) • 𝟙 _) :=
      by simp [Linear.smul_comp, Linear.comp_smul]
    simpa [coe_smul, coe_extendScalarsObj] using (apply_tmul_of_comm f hcomm 1 z.val).symm
@[simp] lemma extendScalarsObj_neg (z : ModuleLocalOrientation N M x d) :
    (-z).extendScalarsObj f = -(z.extendScalarsObj f) := by
  have hz : -z = (-1 : Rˣ) • z := Subtype.ext (neg_one_smul R z.val).symm
  rw [hz, extendScalarsObj_smul]; exact Subtype.ext (by simp)
/-- Exact extension of scalars along `f : R →+* S` on local `R`-orientations. -/
def extendScalars (z : ModuleLocalOrientation (of R R) M x d) :
    ModuleLocalOrientation (of S S) M x d :=
  equivOfCoefficientsIso ((εIso (ModuleCat.extendScalars.{w} f)).symm : _ ≅ of S S) x d
    (z.extendScalarsObj f)
@[simp] lemma coe_extendScalars (z : ModuleLocalOrientation (of R R) M x d) :
    (z.extendScalars f).val =
      (localHomologyExtendScalarsIso f {x} d).hom ((1 : S) ⊗ₜ[R, f] z.val) :=
  ((congr_hom (localHomologyExtendScalarsIso_hom f {x} d) _).trans (comp_apply _ _ _)).symm
@[simp] lemma extendScalars_smul (u : Rˣ) (z : ModuleLocalOrientation (of R R) M x d) :
    (u • z).extendScalars f = Units.map f.toMonoidHom u • z.extendScalars f := by
  simp [extendScalars]
@[simp] lemma extendScalars_neg (z : ModuleLocalOrientation (of R R) M x d) :
    (-z).extendScalars f = -(z.extendScalars f) := by simp [extendScalars]
end ModuleLocalOrientation
end LocalExtendScalars
/-- An *`N`-orientation* of `M` in degree `d`: a transport-invariant choice of local `N`-orientation
at each point of `M` (Hatcher, Section 3.3). -/
structure ModuleOrientation {R : Type u} [Ring R] (N : ModuleCat.{w} R) (M E : Type w)
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (d : ℕ) where
  /-- The local `N`-orientation at each point of `M`. -/
  toFun (x : M) : ModuleLocalOrientation N M x d
  /-- Transport along any path class carries the local orientation at its start to its end. -/
  moduleLocalOrientationTransport_toFun' {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    moduleLocalOrientationTransport N M E d f (toFun x.as) = toFun y.as
namespace ModuleOrientation
open ModuleLocalOrientation (coe_equivOfCoefficientsIso coe_extendScalarsObj)
open IsOpenEmbedding (coe_moduleLocalOrientationEquiv)
variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
section General
variable {R : Type u} [Ring R] {N : ModuleCat.{w} R} {d : ℕ}
instance : DFunLike (ModuleOrientation N M E d) M (fun x ↦ ModuleLocalOrientation N M x d) :=
  ⟨toFun, fun | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl⟩
@[simp] theorem toFun_eq_coe (o : ModuleOrientation N M E d) : o.toFun = o := (rfl)
@[simp] theorem coe_mk (o : ∀ x : M, ModuleLocalOrientation N M x d)
    (h : ∀ {x y : FundamentalGroupoid M} (f : x ⟶ y),
      moduleLocalOrientationTransport N M E d f (o x.as) = o y.as) :
    ⇑(⟨o, h⟩ : ModuleOrientation N M E d) = o := (rfl)
@[ext] theorem ext {o o' : ModuleOrientation N M E d} (h : ∀ x, o x = o' x) : o = o' :=
  DFunLike.ext _ _ h
@[simp] theorem moduleLocalOrientationTransport_apply (o : ModuleOrientation N M E d)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    moduleLocalOrientationTransport N M E d f (o x.as) = o y.as :=
  o.moduleLocalOrientationTransport_toFun' f
/-- On local homology classes, `o` is invariant under `TauCeti.localHomologyTransport`. -/
@[simp] theorem localHomologyTransport_coe_apply (o : ModuleOrientation N M E d)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport N M E d f (o x.as).val = (o y.as).val := by
  rw [← coe_moduleLocalOrientationTransport, moduleLocalOrientationTransport_apply]
instance : MulAction Rˣ (ModuleOrientation N M E d) :=
  { smul := fun u o ↦ ⟨fun x ↦ u • o x, fun f ↦ by
      rw [moduleLocalOrientationTransport_smul, moduleLocalOrientationTransport_apply]⟩
    one_smul := fun o ↦ ext fun x ↦ one_smul Rˣ (o x)
    mul_smul := fun u v o ↦ ext fun x ↦ mul_smul u v (o x) }
instance : InvolutiveNeg (ModuleOrientation N M E d) :=
  { neg := fun o ↦ ⟨fun x ↦ -o x, fun f ↦ by
      rw [moduleLocalOrientationTransport_neg, moduleLocalOrientationTransport_apply]⟩
    neg_neg := fun o ↦ ext fun x ↦ neg_neg (o x) }
@[simp] theorem smul_apply (u : Rˣ) (o : ModuleOrientation N M E d) (x : M) :
    (u • o) x = u • o x := (rfl)
@[simp] theorem neg_apply (o : ModuleOrientation N M E d) (x : M) : (-o) x = -o x := (rfl)
private def mapOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N')
    (o : ModuleOrientation N M E d) : ModuleOrientation N' M E d :=
  ⟨fun x ↦ ModuleLocalOrientation.equivOfCoefficientsIso e x d (o x), fun {x _} f ↦ Subtype.ext <|
    by simpa [o.localHomologyTransport_coe_apply f] using (congr_hom
      (localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom (E := E) e d f)
      (o x.as).val).symm⟩
private lemma mapOfCoefficientsIso_apply {N' : ModuleCat.{w} R} (e : N ≅ N')
    (o : ModuleOrientation N M E d) (x : M) :
    mapOfCoefficientsIso e o x = ModuleLocalOrientation.equivOfCoefficientsIso e x d (o x) := (rfl)
/-- An iso `e : N ≅ N'` induces an equivalence between `N`-orientations and `N'`-orientations. -/
def equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N') :
    ModuleOrientation N M E d ≃ ModuleOrientation N' M E d :=
  ⟨mapOfCoefficientsIso e, mapOfCoefficientsIso e.symm, fun _ ↦ ext fun _ ↦ Subtype.ext <| by
     simp [mapOfCoefficientsIso_apply, ← comp_apply, ← localHomologyMapOfCoefficients_comp],
   fun _ ↦ ext fun _ ↦ Subtype.ext <| by
     simp [mapOfCoefficientsIso_apply, ← comp_apply, ← localHomologyMapOfCoefficients_comp]⟩
section
variable {N' : ModuleCat.{w} R} (e : N ≅ N')
@[simp] theorem equivOfCoefficientsIso_apply (o : ModuleOrientation N M E d) (x : M) :
    equivOfCoefficientsIso e o x =
      ModuleLocalOrientation.equivOfCoefficientsIso e x d (o x) := (rfl)
@[simp] theorem equivOfCoefficientsIso_symm_apply (o : ModuleOrientation N' M E d) (x : M) :
    (equivOfCoefficientsIso e).symm o x =
      (ModuleLocalOrientation.equivOfCoefficientsIso e x d).symm (o x) := Subtype.ext <| by
  dsimp only [equivOfCoefficientsIso, Equiv.coe_fn_symm_mk]; simp [mapOfCoefficientsIso_apply]
@[simp] theorem equivOfCoefficientsIso_smul (u : Rˣ) (o : ModuleOrientation N M E d) :
    equivOfCoefficientsIso e (u • o) = u • equivOfCoefficientsIso e o := ext fun _ ↦ by simp
@[simp] theorem equivOfCoefficientsIso_neg (o : ModuleOrientation N M E d) :
    equivOfCoefficientsIso e (-o) = -equivOfCoefficientsIso e o := ext fun _ ↦ by simp
end
/-- **An `N`-orientation of a connected manifold is determined by its value at one point.** -/
theorem eq_of_apply_eq [ConnectedSpace M] {o o' : ModuleOrientation N M E d} {x : M}
    (h : o x = o' x) : o = o' := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M); refine ext fun y ↦ ?_
  have hf := congrArg (moduleLocalOrientationTransport N M E d
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y) :
      FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)) h
  rwa [moduleLocalOrientationTransport_apply, moduleLocalOrientationTransport_apply] at hf
/-- Over a Dedekind-finite ring `R`, `Rˣ` acts pretransitively on connected `n`-manifolds. -/
theorem exists_units_smul_eq {R : Type w} [Ring R] [IsDedekindFiniteMonoid R] [ConnectedSpace M]
    (hd : finrank ℝ E = d) (o o' : ModuleOrientation (of R R) M E d) : ∃ u : Rˣ, u • o = o' := by
  subst hd; obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  obtain ⟨u, hu⟩ := (singularHomologyComplSingletonFinrankIso (of R R) (chartAt E x)
    (mem_chart_source E x)).toLinearEquiv.exists_units_smul_eq_of_span_singleton_eq_top
      (o x).property (o' x).property
  exact ⟨u, eq_of_apply_eq (x := x) (Subtype.ext hu)⟩
/-- On a nonempty `n`-manifold (`[CommRing R]`, faithful `N`), `Rˣ` acts freely. -/
theorem units_smul_injective {R : Type u} [CommRing R] {N : ModuleCat.{w} R} [FaithfulSMul R N]
    [Nonempty M] (hd : finrank ℝ E = d) (o : ModuleOrientation N M E d) :
    Function.Injective fun u : Rˣ ↦ u • o :=
  let ⟨x⟩ := ‹Nonempty M›; fun _ _ huv ↦ (o x).units_smul_injective hd (DFunLike.congr_fun huv x)
section Transport
variable [PathConnectedSpace M]
/-- **Orientations by transport.** On a path-connected manifold, a local `N`-orientation `z` at `x`
whose transport along path classes from `x` depends only on their end extends to an
`N`-orientation. -/
def ofLocalOrientationTransport (x : M) (z : ModuleLocalOrientation N M x d)
    (h : ∀ {y : FundamentalGroupoid M} (f g : FundamentalGroupoid.mk x ⟶ y),
      moduleLocalOrientationTransport N M E d f z = moduleLocalOrientationTransport N M E d g z) :
    ModuleOrientation N M E d where
  toFun y := moduleLocalOrientationTransport N M E d
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y) :
      FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) z
  moduleLocalOrientationTransport_toFun' _ := by
    rw [← Equiv.trans_apply, ← moduleLocalOrientationTransport_comp]; exact h _ _
theorem ofLocalOrientationTransport_apply (x : M) (z : ModuleLocalOrientation N M x d)
    (h : ∀ {y : FundamentalGroupoid M} (f g : FundamentalGroupoid.mk x ⟶ y),
      moduleLocalOrientationTransport N M E d f z = moduleLocalOrientationTransport N M E d g z)
    (y : M) (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ofLocalOrientationTransport (E := E) x z h y = moduleLocalOrientationTransport N M E d f z :=
  h _ f
@[simp] theorem ofLocalOrientationTransport_apply_self (x : M)
    (z : ModuleLocalOrientation N M x d)
    (h : ∀ {y : FundamentalGroupoid M} (f g : FundamentalGroupoid.mk x ⟶ y),
      moduleLocalOrientationTransport N M E d f z = moduleLocalOrientationTransport N M E d g z) :
    ofLocalOrientationTransport (E := E) x z h x = z := by
  rw [ofLocalOrientationTransport_apply x z h x (𝟙 _), moduleLocalOrientationTransport_id]; rfl
end Transport
section SimplyConnected
variable [SimplyConnectedSpace M]
section
variable (x : M) (z : ModuleLocalOrientation N M x d)
private theorem moduleLocalOrientationTransport_eq_of_simplyConnectedSpace
    {y : FundamentalGroupoid M} (f g : FundamentalGroupoid.mk x ⟶ y) :
    moduleLocalOrientationTransport N M E d f z = moduleLocalOrientationTransport N M E d g z :=
  congrArg (moduleLocalOrientationTransport N M E d · z)
    (Subsingleton.elim (α := Path.Homotopic.Quotient x _) f g)
/-- **Simply connected manifold**: extend a local orientation globally by path transport. -/
def ofSimplyConnectedSpace : ModuleOrientation N M E d :=
  ofLocalOrientationTransport x z (moduleLocalOrientationTransport_eq_of_simplyConnectedSpace x z)
theorem ofSimplyConnectedSpace_apply (y : M)
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ofSimplyConnectedSpace (E := E) x z y = moduleLocalOrientationTransport N M E d f z :=
  ofLocalOrientationTransport_apply x z
    (moduleLocalOrientationTransport_eq_of_simplyConnectedSpace x z) y f
@[simp] theorem ofSimplyConnectedSpace_apply_self : ofSimplyConnectedSpace (E := E) x z x = z :=
  ofLocalOrientationTransport_apply_self x z
    (moduleLocalOrientationTransport_eq_of_simplyConnectedSpace x z)
end
/-- Every simply connected `n`-manifold has an `R`-orientation over any ring `R`. -/
theorem nonempty_of_simplyConnectedSpace {R : Type w} [Ring R] (hd : finrank ℝ E = d) :
    Nonempty (ModuleOrientation (of R R) M E d) := let ⟨x⟩ := (inferInstance : Nonempty M)
  ⟨ofSimplyConnectedSpace x (ModuleLocalOrientation.nonempty_of_finrank_eq x hd).some⟩
end SimplyConnected
section OpenEmbedding
variable {M' M'' : Type w} [TopologicalSpace M'] [T2Space M'] [TopologicalSpace M''] [T2Space M'']
  [ChartedSpace E M'] [ChartedSpace E M''] {j : M → M'}
section
variable (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j)
/-- The **pullback of an `N`-orientation along an open embedding** `j : M → M'`. -/
def comap : ModuleOrientation N M E d :=
  ⟨fun x ↦ (hj.moduleLocalOrientationEquiv N x d).symm (o (j x)), fun {x y} f ↦
    (hj.moduleLocalOrientationEquiv N y.as d).injective <| by
      rw [Equiv.apply_symm_apply]; apply Subtype.ext
      have h : (localHomologyIsoOfIsOpenEmbedding N hj y.as d).hom
          (localHomologyTransport N M E d f
            ((hj.moduleLocalOrientationEquiv N x.as d).symm (o (j x.as))).val) =
          localHomologyTransport N M' E d ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f)
            ((localHomologyIsoOfIsOpenEmbedding N hj x.as d).hom
              ((hj.moduleLocalOrientationEquiv N x.as d).symm (o (j x.as))).val) :=
        (comp_apply _ _ _).symm.trans ((congr_hom
          (localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom N (E := E) hj d f)
          _).trans (comp_apply _ _ _))
      rw [coe_moduleLocalOrientationEquiv, coe_moduleLocalOrientationTransport, h,
        ← coe_moduleLocalOrientationEquiv, Equiv.apply_symm_apply]
      exact o.localHomologyTransport_coe_apply ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f)⟩
lemma comap_apply (x : M) : o.comap hj x = (hj.moduleLocalOrientationEquiv N x d).symm (o (j x)) :=
  (rfl)
@[simp] lemma moduleLocalOrientationEquiv_comap_apply (x : M) :
    hj.moduleLocalOrientationEquiv N x d (o.comap hj x) = o (j x) := Equiv.apply_symm_apply _ _
@[simp] lemma comap_neg : (-o).comap hj = -o.comap hj :=
  ext fun x ↦ (hj.moduleLocalOrientationEquiv N x d).injective (by simp)
end
lemma comap_congr (o : ModuleOrientation N M' E d) {j' : M → M'} (hj : IsOpenEmbedding j)
    (hj' : IsOpenEmbedding j') (hjj' : j = j') : o.comap hj = o.comap hj' := by subst hjj'; rfl
@[simp] lemma comap_smul (u : Rˣ) (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j) :
    (u • o).comap hj = u • o.comap hj :=
  ext fun x ↦ (hj.moduleLocalOrientationEquiv N x d).injective (by simp)
@[simp] lemma comap_id (o : ModuleOrientation N M E d) : o.comap IsOpenEmbedding.id = o :=
  ext fun x ↦ (IsOpenEmbedding.id.moduleLocalOrientationEquiv N x d).injective <| by
    rw [moduleLocalOrientationEquiv_comap_apply, IsOpenEmbedding.moduleLocalOrientationEquiv_id,
      Equiv.refl_apply]; rfl
lemma comap_comap (o : ModuleOrientation N M'' E d) {j' : M' → M''} (hj' : IsOpenEmbedding j')
    (hj : IsOpenEmbedding j) : (o.comap hj').comap hj = o.comap (hj'.comp hj) :=
  ext fun x ↦ ((hj'.comp hj).moduleLocalOrientationEquiv N x d).injective <| by
    rw [moduleLocalOrientationEquiv_comap_apply, ← IsOpenEmbedding.moduleLocalOrientationEquiv_trans
      hj hj', Equiv.trans_apply, moduleLocalOrientationEquiv_comap_apply,
      moduleLocalOrientationEquiv_comap_apply]; rfl
@[simp] lemma comap_symm_comap (o : ModuleOrientation N M' E d) (e : M ≃ₜ M') :
    (o.comap e.isOpenEmbedding).comap e.symm.isOpenEmbedding = o := by
  rw [comap_comap, o.comap_congr _ IsOpenEmbedding.id (funext e.apply_symm_apply), comap_id]
lemma comap_equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N')
    (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j) :
    (equivOfCoefficientsIso e o).comap hj = equivOfCoefficientsIso e (o.comap hj) := by
  ext x : 1; apply (hj.moduleLocalOrientationEquiv N' x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply]; apply Subtype.ext
  have hjx : (⟨j, hj.continuous⟩ : C(M, M')) ⁻¹' {j x} ⊆ {x} := fun _ hy ↦ hj.injective hy
  have h := congr_hom (localHomologyMap_comp_localHomologyIsoOfCoefficientsIso_hom e
    ⟨j, hj.continuous⟩ hjx d) (o.comap hj x).val; simp only [comp_apply] at h
  rw [coe_moduleLocalOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
    equivOfCoefficientsIso_apply, coe_equivOfCoefficientsIso, equivOfCoefficientsIso_apply,
    coe_equivOfCoefficientsIso, ← h, comap_apply,
    hj.localHomologyMap_moduleLocalOrientationEquiv_symm N x (o (j x)) hjx]
end OpenEmbedding
end General
section ExtendScalars
variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{w} f)] {d : ℕ}
section Obj
variable {N : ModuleCat.{w} R}
section
variable (o : ModuleOrientation N M E d)
/-- **Extension of scalars** of an `N`-orientation along exact `f : R →+* S`. -/
def extendScalarsObj : ModuleOrientation ((ModuleCat.extendScalars.{w} f).obj N) M E d :=
  ⟨fun x ↦ (o x).extendScalarsObj f, fun g ↦ Subtype.ext <| by
    rw [coe_moduleLocalOrientationTransport, coe_extendScalarsObj, coe_extendScalarsObj]
    exact (apply_tmul_of_comm f (map_localHomologyTransport_comp_localHomologyObjIso_hom (E := E)
        (ModuleCat.extendScalars.{w} f) N d g) 1 (o _).val).trans
      (congrArg _ (congrArg ((1 : S) ⊗ₜ[R, f] ·) (o.localHomologyTransport_coe_apply g)))⟩
@[simp] lemma extendScalarsObj_apply (x : M) : o.extendScalarsObj f x = (o x).extendScalarsObj f :=
  (rfl)
lemma coe_extendScalarsObj_apply (x : M) : (o.extendScalarsObj f x).val =
    (localHomologyObjIso (ModuleCat.extendScalars.{w} f) N {x} d).hom ((1 : S) ⊗ₜ[R, f] (o x).val)
    := (rfl)
@[simp] lemma extendScalarsObj_neg : (-o).extendScalarsObj f = -(o.extendScalarsObj f) :=
  ext fun _ ↦ by simp
end
@[simp] lemma extendScalarsObj_smul (u : Rˣ) (o : ModuleOrientation N M E d) :
    (u • o).extendScalarsObj f = Units.map f.toMonoidHom u • o.extendScalarsObj f :=
  ext fun _ ↦ by simp
lemma comap_extendScalarsObj {M' : Type w} [TopologicalSpace M'] [T2Space M'] [ChartedSpace E M']
    (o : ModuleOrientation N M' E d) {j : M → M'} (hj : IsOpenEmbedding j) :
    (o.extendScalarsObj f).comap hj = (o.comap hj).extendScalarsObj f := by
  ext x : 1
  apply (hj.moduleLocalOrientationEquiv ((ModuleCat.extendScalars.{w} f).obj N) x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply]; apply Subtype.ext
  have hjx : (⟨j, hj.continuous⟩ : C(M, M')) ⁻¹' {j x} ⊆ {x} := fun _ hy ↦ hj.injective hy
  rw [coe_moduleLocalOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom,
    coe_extendScalarsObj_apply, coe_extendScalarsObj_apply]
  exact ((apply_tmul_of_comm f (map_localHomologyMap_comp_localHomologyObjIso_hom
      (ModuleCat.extendScalars.{w} f) N ⟨j, hj.continuous⟩ hjx d) 1 (o.comap hj x).val).trans
    (congrArg _ (congrArg ((1 : S) ⊗ₜ[R, f] ·)
      (hj.localHomologyMap_moduleLocalOrientationEquiv_symm N x (o (j x)) hjx)))).symm
end Obj
section
variable (o : ModuleOrientation (of R R) M E d)
/-- **Extension of scalars** of an `R`-orientation along exact `f : R →+* S`. -/
def extendScalars : ModuleOrientation (of S S) M E d :=
  equivOfCoefficientsIso ((εIso (ModuleCat.extendScalars.{w} f)).symm : _ ≅ of S S)
    (o.extendScalarsObj f)
lemma extendScalars_def : o.extendScalars f =
    equivOfCoefficientsIso ((εIso (ModuleCat.extendScalars.{w} f)).symm : _ ≅ of S S)
      (o.extendScalarsObj f) := (rfl)
@[simp] lemma extendScalars_apply (x : M) : o.extendScalars f x = (o x).extendScalars f := (rfl)
lemma coe_extendScalars_apply (x : M) : (o.extendScalars f x).val =
    (localHomologyExtendScalarsIso f {x} d).hom ((1 : S) ⊗ₜ[R, f] (o x).val) :=
  (o x).coe_extendScalars f
@[simp] lemma extendScalars_neg : (-o).extendScalars f = -(o.extendScalars f) := by
  simp [extendScalars]
end
@[simp] lemma extendScalars_smul (u : Rˣ) (o : ModuleOrientation (of R R) M E d) :
    (u • o).extendScalars f = Units.map f.toMonoidHom u • o.extendScalars f := by
  simp [extendScalars]
lemma comap_extendScalars {M' : Type w} [TopologicalSpace M'] [T2Space M'] [ChartedSpace E M']
    (o : ModuleOrientation (of R R) M' E d) {j : M → M'} (hj : IsOpenEmbedding j) :
    (o.extendScalars f).comap hj = (o.comap hj).extendScalars f := by
  simp only [extendScalars, comap_equivOfCoefficientsIso, comap_extendScalarsObj]
end ExtendScalars
section Canonical
variable {n : ℕ}
section
variable {K : Type w} [Ring K] [IsDedekindFiniteMonoid K] [Subsingleton Kˣ] (hn : finrank ℝ E = n)
/-- **Canonical `K`-orientation** for a Dedekind-finite ring `K` with `[Subsingleton Kˣ]`. -/
def ofSubsingletonUnits : ModuleOrientation (of K K) M E n :=
  ⟨fun x ↦ (ModuleLocalOrientation.uniqueOfSubsingletonUnits (E := E) x hn).default,
   fun {_ y} _ ↦ by
     have := ModuleLocalOrientation.uniqueOfSubsingletonUnits (M := M) (E := E) (K := K) y.as hn
     exact Subsingleton.elim _ _⟩
/-- Unique `K`-orientation on an `n`-manifold for Dedekind-finite `K` with `[Subsingleton Kˣ]`. -/
@[instance_reducible] def uniqueOfSubsingletonUnits : Unique (ModuleOrientation (of K K) M E n) :=
  ⟨⟨ofSubsingletonUnits hn⟩, fun _ ↦ ext fun x ↦ by
    have := ModuleLocalOrientation.uniqueOfSubsingletonUnits (M := M) (E := E) (K := K) x hn
    exact Subsingleton.elim _ _⟩
end
section
variable {R : Type w} [CommRing R] (hn : finrank ℝ E = n) (h2 : (2 : R) = 0)
/-- **Canonical `R`-orientation for a commutative ring `R` with `(2 : R) = 0`**: scalar extension
along `ZMod.castULiftHom R : ULift (ZMod 2) →+* R` from `ULift (ZMod 2)` (Hatcher, §3.3). -/
def ofTwoEqZero : ModuleOrientation (of R R) M E n := letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  (ofSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn).extendScalars
    (ZMod.castULiftHom.{w} (n := 2) R (by simpa using h2))
theorem ofTwoEqZero_def [PreservesFiniteLimits (ModuleCat.extendScalars.{w}
    (ZMod.castULiftHom.{w} (n := 2) R (by simpa using h2)))] : ofTwoEqZero (M := M) (E := E) hn h2 =
      (ofSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn).extendScalars
        (ZMod.castULiftHom.{w} (n := 2) R (by simpa using h2)) := by unfold ofTwoEqZero; rfl
theorem ofTwoEqZero_eq_extendScalars (f : ULift.{w} (ZMod 2) →+* R)
    [PreservesFiniteLimits (ModuleCat.extendScalars.{w} f)] : ofTwoEqZero (M := M) (E := E) hn h2 =
      (ofSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn).extendScalars f := by
  have hf : f = ZMod.castULiftHom.{w} (n := 2) R (by simpa using h2) := Subsingleton.elim _ _
  subst hf; exact ofTwoEqZero_def hn h2
@[simp] theorem neg_ofTwoEqZero :
    -(ofTwoEqZero (M := M) (E := E) hn h2) = ofTwoEqZero (M := M) (E := E) hn h2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; rw [ofTwoEqZero_def, ← extendScalars_neg]
  have := uniqueOfSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn
  exact congrArg _ (Subsingleton.elim _ _)
theorem ofTwoEqZero_eq_ofSubsingletonUnits [Subsingleton Rˣ] :
    ofTwoEqZero (M := M) (E := E) hn h2 = ofSubsingletonUnits (M := M) (E := E) hn := by
  have := uniqueOfSubsingletonUnits (M := M) (E := E) (K := R) hn; exact Subsingleton.elim _ _
@[simp] theorem comap_ofTwoEqZero {M' : Type w} [TopologicalSpace M'] [T2Space M']
    [ChartedSpace E M'] {j : M → M'} (hj : IsOpenEmbedding j) :
    (ofTwoEqZero (M := M') hn h2).comap hj = ofTwoEqZero (M := M) hn h2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ofTwoEqZero_def, ofTwoEqZero_def, comap_extendScalars]
  have := uniqueOfSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn
  exact congrArg _ (Subsingleton.elim _ _)
end
end Canonical
end ModuleOrientation
end TauCeti
