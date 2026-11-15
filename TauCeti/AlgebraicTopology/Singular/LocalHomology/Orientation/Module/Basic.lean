/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Coefficients
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.OpenEmbedding
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import TauCeti.Algebra.GroupWithZero.Units.Basic

/-!
# Module orientations of manifolds

Let `M` be a Hausdorff space modelled on a finite-dimensional real normed space `E`, `R` a ring and
`N` an `R`-module. A *local `N`-orientation* at `x ∈ M` in degree `d`
(`TauCeti.ModuleLocalOrientation N M x d`) is a single-element generator of the local homology
`H_d(M, M ∖ {x}; N)` as an `R`-module, and an *`N`-orientation* of `M` in degree `d`
(`TauCeti.ModuleOrientation N M E d`) is a transport-invariant choice of local `N`-orientation at
every point `x` of `M`.

For `N = R` in the dimension `d = finrank ℝ E` of the manifold, this is an *`R`-orientation* in the
sense of Hatcher, Section 3.3, pp. 235–236: the chart isomorphism identifies `H_d(M, M ∖ {x}; R)`
with `R`, so the local `R`-orientations at `x` correspond to the units `Rˣ`
(`TauCeti.ModuleLocalOrientation.equivUnits`), and `Rˣ` acts transitively on the `R`-orientations
of a connected manifold (`TauCeti.ModuleOrientation.exists_units_smul_eq`). With integral
coefficients `ULift ℤ`, `N`-orientations are canonically equivalent to
`TauCeti.HomologicalOrientation` (`TauCeti.ModuleOrientation.equivHomologicalOrientation`).

When `1` is the only unit of a commutative ring `K` (`Subsingleton Kˣ`), every `n`-manifold has a
unique `K`-orientation (`TauCeti.ModuleOrientation.uniqueOfSubsingletonUnits`). Exact extension of
scalars along `f : R →+* S` carries `R`-orientations to `S`-orientations
(`TauCeti.ModuleOrientation.extendScalars`). Combining both for the flat map from `ULift (ZMod 2)`
gives a canonical `R`-orientation on every topological `n`-manifold whenever `(2 : R) = 0`
(`TauCeti.ModuleOrientation.ofTwoEqZero`), without any orientability assumption on `M`.

## Main definitions

* `TauCeti.IsModuleLocalOrientation`, `TauCeti.ModuleLocalOrientation`: generators of the local
  homology `H_d(M, M ∖ {x}; N)` as an `R`-module.
* `TauCeti.moduleLocalOrientationTransport`: transport of local `N`-orientations along paths.
* `Topology.IsOpenEmbedding.moduleLocalOrientationEquiv`: excision correspondence of local
  `N`-orientations along an open embedding.
* `TauCeti.ModuleOrientation`: transport-invariant families of local `N`-orientations on a
  manifold.
* `TauCeti.ModuleOrientation.equivHomologicalOrientation`: equivalence with
  `TauCeti.HomologicalOrientation` for integral coefficients `ULift ℤ`.
* `TauCeti.ModuleOrientation.comap`: pullback of an `N`-orientation along an open embedding.
* `TauCeti.ModuleOrientation.extendScalars`: change of coefficients of an `R`-orientation along a
  ring homomorphism `f : R →+* S` whose extension of scalars preserves finite limits.
* `TauCeti.ModuleOrientation.ofSubsingletonUnits`: the unique `K`-orientation of an `n`-manifold
  when `Subsingleton Kˣ`.
* `TauCeti.ModuleOrientation.ofTwoEqZero`: the canonical `R`-orientation of an `n`-manifold over a
  commutative ring `R` with `(2 : R) = 0`.

## Main results

* `TauCeti.ModuleLocalOrientation.equivUnits`: an isomorphism `H_d(M, M ∖ {x}; R) ≅ R` identifies
  local `R`-orientations with `Rˣ`.
* `TauCeti.ModuleOrientation.eq_of_apply_eq`: on a connected manifold, an `N`-orientation is
  determined by its value at one point.
* `TauCeti.ModuleOrientation.exists_units_smul_eq`,
  `TauCeti.ModuleOrientation.units_smul_injective`: on a nonempty connected `n`-manifold over a
  commutative ring `R`, `Rˣ` acts freely and transitively on `R`-orientations.
* `TauCeti.ModuleOrientation.nonempty_of_simplyConnectedSpace`: a simply connected `n`-manifold has
  an `R`-orientation over every ring `R`.
* `TauCeti.ModuleOrientation.uniqueOfSubsingletonUnits`: an `n`-manifold has a unique
  `K`-orientation when `Subsingleton Kˣ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, pp. 235–236.
-/

public section

noncomputable section

open CategoryTheory Limits Module Topology
open scoped ChangeOfRings

universe w u

namespace TauCeti

section Local

variable {M M' : Type w} [TopologicalSpace M] [TopologicalSpace M']
  {R : Type u} [Ring R] (N : ModuleCat.{w} R)

/-- An element of the local homology `H_d(M, M ∖ {x}; N)` is a *local `N`-orientation* when it
generates the whole group as an `R`-module. -/
def IsModuleLocalOrientation (x : M) (d : ℕ)
    (z : (localHomology N ({x} : Set M) d : ModuleCat.{w} R)) : Prop :=
  Submodule.span R {z} = ⊤

theorem isModuleLocalOrientation_iff (x : M) (d : ℕ)
    (z : (localHomology N ({x} : Set M) d : ModuleCat.{w} R)) :
    IsModuleLocalOrientation N x d z ↔ Submodule.span R {z} = ⊤ :=
  Iff.rfl

/-- The subtype of local `N`-orientations inside the local homology `H_d(M, M ∖ {x}; N)`. -/
abbrev ModuleLocalOrientation (M : Type w) [TopologicalSpace M] (x : M) (d : ℕ) :=
  {z : (localHomology N ({x} : Set M) d : ModuleCat.{w} R) // IsModuleLocalOrientation N x d z}

variable {N}

/-- An `R`-module isomorphism of local homology groups preserves local `N`-orientations. -/
theorem IsModuleLocalOrientation.map {N' : ModuleCat.{w} R} {x : M} {y : M'} {d : ℕ}
    {z : (localHomology N ({x} : Set M) d : ModuleCat.{w} R)}
    (hz : IsModuleLocalOrientation N x d z)
    (e : localHomology N ({x} : Set M) d ≅ localHomology N' ({y} : Set M') d) :
    IsModuleLocalOrientation N' y d (e.hom z) :=
  (ModuleCat.span_singleton_apply_eq_top_iff e.hom).2 hz

/-- Multiplying by a unit of `R` preserves local `N`-orientations. -/
theorem isModuleLocalOrientation_smul_iff_of_isUnit {x : M} {d : ℕ} {r : R} (hr : IsUnit r)
    {z : (localHomology N ({x} : Set M) d : ModuleCat.{w} R)} :
    IsModuleLocalOrientation N x d (r • z) ↔ IsModuleLocalOrientation N x d z := by
  simp only [isModuleLocalOrientation_iff, Submodule.span_singleton_smul_eq hr]

/-- Reversing a class preserves whether it is a local `N`-orientation. -/
theorem IsModuleLocalOrientation.neg {x : M} {d : ℕ}
    {z : (localHomology N ({x} : Set M) d : ModuleCat.{w} R)}
    (hz : IsModuleLocalOrientation N x d z) : IsModuleLocalOrientation N x d (-z) := by
  rw [← neg_one_smul R z]
  exact (isModuleLocalOrientation_smul_iff_of_isUnit isUnit_one.neg).2 hz

instance {x : M} {d : ℕ} : MulAction Rˣ (ModuleLocalOrientation N M x d) where
  smul u z := ⟨(u : R) • z.val, (isModuleLocalOrientation_smul_iff_of_isUnit u.isUnit).2 z.property⟩
  one_smul z := Subtype.ext (one_smul R z.val)
  mul_smul u v z := Subtype.ext (mul_smul (u : R) (v : R) z.val)

@[simp]
lemma ModuleLocalOrientation.coe_smul {x : M} {d : ℕ} (u : Rˣ)
    (z : ModuleLocalOrientation N M x d) :
    (u • z).val = (u : R) • z.val :=
  (rfl)

instance {x : M} {d : ℕ} : InvolutiveNeg (ModuleLocalOrientation N M x d) where
  neg z := ⟨-z.val, z.property.neg⟩
  neg_neg z := Subtype.ext (neg_neg z.val)

@[simp]
lemma ModuleLocalOrientation.coe_neg {x : M} {d : ℕ} (z : ModuleLocalOrientation N M x d) :
    (-z).val = -z.val :=
  (rfl)

/-- An isomorphism of coefficient modules `e : N ≅ N'` identifies local `N`-orientations with local
`N'`-orientations. -/
def ModuleLocalOrientation.equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N') (x : M)
    (d : ℕ) : ModuleLocalOrientation N M x d ≃ ModuleLocalOrientation N' M x d :=
  let iso := localHomologyIsoOfCoefficientsIso e ({x} : Set M) d
  iso.toLinearEquiv.toEquiv.subtypeEquiv fun z ↦
    ⟨fun hz ↦ hz.map iso, fun hz ↦ (iso.hom_inv_id_apply z) ▸ hz.map iso.symm⟩

@[simp]
lemma ModuleLocalOrientation.coe_equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N')
    (x : M) (d : ℕ) (z : ModuleLocalOrientation N M x d) :
    (ModuleLocalOrientation.equivOfCoefficientsIso e x d z).val =
      (localHomologyIsoOfCoefficientsIso e ({x} : Set M) d).hom z.val :=
  (rfl)

/-- With integral coefficients `ULift ℤ`, `IsModuleLocalOrientation` coincides with
`IsLocalOrientation`. -/
theorem isModuleLocalOrientation_iff_isLocalOrientation (x : M) (d : ℕ)
    (z : (localHomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ({x} : Set M) d : ModuleCat.{w} ℤ)) :
    IsModuleLocalOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) x d z ↔
      IsLocalOrientation x d z := by
  rw [isModuleLocalOrientation_iff, Submodule.span_singleton_eq_top_iff, isLocalOrientation_iff]
  exact forall_congr' fun _ ↦ exists_congr fun c ↦
    iff_of_eq (congrArg (· = _) (int_smul_eq_zsmul _ c _))

/-- With integral coefficients `ULift ℤ`, local module orientations are canonically equivalent to
`TauCeti.LocalOrientation`. -/
def ModuleLocalOrientation.equivLocalOrientation (M : Type w) [TopologicalSpace M] (x : M)
    (d : ℕ) : ModuleLocalOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) M x d ≃
      LocalOrientation M x d :=
  Equiv.subtypeEquivRight (isModuleLocalOrientation_iff_isLocalOrientation x d)

@[simp]
lemma ModuleLocalOrientation.coe_equivLocalOrientation (x : M) (d : ℕ)
    (z : ModuleLocalOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) M x d) :
    (ModuleLocalOrientation.equivLocalOrientation M x d z).val = z.val :=
  (rfl)

@[simp]
lemma ModuleLocalOrientation.coe_equivLocalOrientation_symm (x : M) (d : ℕ)
    (z : LocalOrientation M x d) :
    ((ModuleLocalOrientation.equivLocalOrientation M x d).symm z).val = z.val :=
  (rfl)

end Local

section BaseRing

variable {M E : Type w} [TopologicalSpace M] {R : Type w} [Ring R]

/-- Under an isomorphism `H_d(M, M ∖ {x}; R) ≅ R`, the preimage of `1` is a local
`R`-orientation. -/
theorem isModuleLocalOrientation_inv_one {x : M} {d : ℕ}
    (e : localHomology (ModuleCat.of R R) ({x} : Set M) d ≅ ModuleCat.of R R) :
    IsModuleLocalOrientation (ModuleCat.of R R) x d (e.inv (1 : R)) :=
  (ModuleCat.span_singleton_apply_eq_top_iff e.inv).2
    ((Ideal.eq_top_iff_one _).2 (Submodule.mem_span_singleton_self 1))

/-- Under an isomorphism `H_d(M, M ∖ {x}; R) ≅ R` over a Dedekind-finite ring, local
`R`-orientations are precisely the classes whose coordinate in `R` is a unit. -/
theorem isModuleLocalOrientation_iff_isUnit [IsDedekindFiniteMonoid R] {x : M} {d : ℕ}
    (e : localHomology (ModuleCat.of R R) ({x} : Set M) d ≅ ModuleCat.of R R)
    (z : (localHomology (ModuleCat.of R R) ({x} : Set M) d : ModuleCat.{w} R)) :
    IsModuleLocalOrientation (ModuleCat.of R R) x d z ↔ IsUnit (e.hom z) :=
  e.toLinearEquiv.span_singleton_eq_top_iff_isUnit

/-- An isomorphism `H_d(M, M ∖ {x}; R) ≅ R` over a Dedekind-finite ring identifies the local
`R`-orientations at `x` with `Rˣ`. -/
def ModuleLocalOrientation.equivUnits [IsDedekindFiniteMonoid R] {x : M} {d : ℕ}
    (e : localHomology (ModuleCat.of R R) ({x} : Set M) d ≅ ModuleCat.of R R) :
    ModuleLocalOrientation (ModuleCat.of R R) M x d ≃ Rˣ where
  toFun z := ((isModuleLocalOrientation_iff_isUnit e z.val).1 z.property).unit
  invFun u := u • ⟨e.inv (1 : R), isModuleLocalOrientation_inv_one e⟩
  left_inv z := Subtype.ext <| by
    have hu : (((isModuleLocalOrientation_iff_isUnit e z.val).1 z.property).unit : R) =
        e.hom z.val :=
      IsUnit.unit_spec _
    calc
      (((((isModuleLocalOrientation_iff_isUnit e z.val).1 z.property).unit : R) •
          e.inv (1 : R))) = e.inv (e.hom z.val • (1 : R)) := by
        rw [hu, map_smul]
      _ = z.val := by
        rw [smul_eq_mul, mul_one, e.hom_inv_id_apply]
  right_inv u := Units.ext <|
    (IsUnit.unit_spec _).trans <| by
      rw [coe_smul, map_smul, e.inv_hom_id_apply, smul_eq_mul, mul_one]

/-- Over a Dedekind-finite ring, any two local `R`-orientations in a fibre isomorphic to `R` differ
by a unit of `R`. -/
theorem ModuleLocalOrientation.exists_units_smul_eq_of_iso [IsDedekindFiniteMonoid R] {x : M}
    {d : ℕ} (e : localHomology (ModuleCat.of R R) ({x} : Set M) d ≅ ModuleCat.of R R)
    (z z' : ModuleLocalOrientation (ModuleCat.of R R) M x d) :
    ∃ u : Rˣ, u • z = z' := by
  let z₀ : ModuleLocalOrientation (ModuleCat.of R R) M x d :=
    ⟨e.inv (1 : R), isModuleLocalOrientation_inv_one e⟩
  have hz : equivUnits e z • z₀ = z := (equivUnits e).symm_apply_apply z
  have hz' : equivUnits e z' • z₀ = z' := (equivUnits e).symm_apply_apply z'
  refine ⟨equivUnits e z' * (equivUnits e z)⁻¹, ?_⟩
  rw [mul_smul]
  nth_rw 2 [← hz]
  rw [inv_smul_smul, hz']

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The local `R`-orientation at `x` selected by a chart `φ` to `E`, uniformly in the dimension
`n = finrank ℝ E`. -/
def moduleLocalOrientationOfChart [T1Space M] (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {n : ℕ} (hn : finrank ℝ E = n) :
    ModuleLocalOrientation (ModuleCat.of R R) M x n :=
  hn ▸ ⟨(singularHomologyComplSingletonFinrankIso (ModuleCat.of R R) φ hx).inv (1 : R),
    isModuleLocalOrientation_inv_one _⟩

/-- Every point of a `T₁` space locally modelled on an `n`-dimensional real normed space has a local
`R`-orientation in degree `n`. -/
theorem ModuleLocalOrientation.nonempty_of_finrank_eq [T1Space M] [ChartedSpace E M] (x : M)
    {n : ℕ} (hn : finrank ℝ E = n) :
    Nonempty (ModuleLocalOrientation (ModuleCat.of R R) M x n) :=
  ⟨moduleLocalOrientationOfChart (chartAt E x) (mem_chart_source E x) hn⟩

/-- At a point of an `n`-manifold, with faithful coefficients `N` over a commutative ring `R`, the
action of `Rˣ` on local `N`-orientations is free. -/
theorem ModuleLocalOrientation.units_smul_injective [T1Space M] [ChartedSpace E M] {R : Type u}
    [CommRing R] {N : ModuleCat.{w} R} [FaithfulSMul R N] {x : M} {n : ℕ} (hn : finrank ℝ E = n)
    (z : ModuleLocalOrientation N M x n) :
    Function.Injective fun u : Rˣ ↦ u • z := by
  subst hn
  intro u v huv
  have hfix : ((u⁻¹ * v : Rˣ) : R) • z.val = z.val := by
    have hval : (u : R) • z.val = (v : R) • z.val := congrArg Subtype.val huv
    calc
      ((u⁻¹ * v : Rˣ) : R) • z.val = (u⁻¹ : Rˣ) • ((v : R) • z.val) := mul_smul _ _ _
      _ = (u⁻¹ : Rˣ) • ((u : R) • z.val) := by rw [← hval]
      _ = z.val := inv_smul_smul u z.val
  -- `u⁻¹ * v` fixes the generator `z`, hence every element of the local homology at `x`.
  have hall (y : (localHomology N ({x} : Set M) (finrank ℝ E) : ModuleCat.{w} R)) :
      ((u⁻¹ * v : Rˣ) : R) • y = y := by
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1
      (z.property.symm ▸ Submodule.mem_top : y ∈ _)
    rw [smul_comm _ t, hfix]
  let e := (singularHomologyComplSingletonFinrankIso N (chartAt E x)
    (mem_chart_source E x)).toLinearEquiv
  have h1 : ((u⁻¹ * v : Rˣ) : R) = 1 :=
    FaithfulSMul.eq_of_smul_eq_smul fun m : N ↦ by
      rw [one_smul, ← e.apply_symm_apply m, ← map_smul, hall]
  exact inv_mul_eq_one.1 (Units.ext h1)

/-- When `1` is the only unit of a commutative ring `K`, each point of an `n`-manifold has a unique
local `K`-orientation in degree `n`. -/
@[instance_reducible]
def ModuleLocalOrientation.uniqueOfSubsingletonUnits {K : Type w} [CommRing K] [Subsingleton Kˣ]
    [T1Space M] [ChartedSpace E M] (x : M) {n : ℕ} (hn : finrank ℝ E = n) :
    Unique (ModuleLocalOrientation (ModuleCat.of K K) M x n) where
  default := moduleLocalOrientationOfChart (chartAt E x) (mem_chart_source E x) hn
  uniq z := by
    subst hn
    exact Subtype.ext
      ((singularHomologyComplSingletonFinrankIso (ModuleCat.of K K) (chartAt E x)
        (mem_chart_source E x)).toLinearEquiv.eq_of_span_singleton_eq_top z.property
        (moduleLocalOrientationOfChart (chartAt E x) (mem_chart_source E x) rfl).property)

end BaseRing

section Transport

variable {R : Type u} [Ring R] (N : ModuleCat.{w} R)
  (M E : Type w) [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  (d : ℕ)

/-- Transport of local `N`-orientations along a path class, obtained by restricting
`TauCeti.localHomologyTransport` to generators. -/
def moduleLocalOrientationTransport {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    ModuleLocalOrientation N M x.as d ≃ ModuleLocalOrientation N M y.as d :=
  let e := (localHomologySystem N M E d).mapIso (asIso f)
  e.toLinearEquiv.toEquiv.subtypeEquiv fun z ↦
    ⟨fun hz ↦ hz.map e, fun hz ↦ (e.hom_inv_id_apply z) ▸ hz.map e.symm⟩

@[simp]
lemma coe_moduleLocalOrientationTransport {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (z : ModuleLocalOrientation N M x.as d) :
    (moduleLocalOrientationTransport N M E d f z).val =
      localHomologyTransport N M E d f z.val :=
  (rfl)

@[simp]
lemma coe_moduleLocalOrientationTransport_symm {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (z : ModuleLocalOrientation N M y.as d) :
    ((moduleLocalOrientationTransport N M E d f).symm z).val =
      localHomologyTransport N M E d (inv f) z.val :=
  (rfl)

@[simp]
lemma moduleLocalOrientationTransport_id (x : FundamentalGroupoid M) :
    moduleLocalOrientationTransport N M E d (𝟙 x) = Equiv.refl _ := by
  ext z : 1
  exact Subtype.ext (by simp)

@[simp]
lemma moduleLocalOrientationTransport_comp {x y z : FundamentalGroupoid M} (f : x ⟶ y)
    (g : y ⟶ z) :
    moduleLocalOrientationTransport N M E d (f ≫ g) =
      (moduleLocalOrientationTransport N M E d f).trans
        (moduleLocalOrientationTransport N M E d g) := by
  ext a : 1
  exact Subtype.ext (by simp [localHomologyTransport_comp])

@[simp]
lemma moduleLocalOrientationTransport_inv {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    moduleLocalOrientationTransport N M E d (inv f) =
      (moduleLocalOrientationTransport N M E d f).symm := by
  ext z : 1
  exact Subtype.ext rfl

@[simp]
lemma moduleLocalOrientationTransport_smul {x y : FundamentalGroupoid M} (f : x ⟶ y) (u : Rˣ)
    (z : ModuleLocalOrientation N M x.as d) :
    moduleLocalOrientationTransport N M E d f (u • z) =
      u • moduleLocalOrientationTransport N M E d f z :=
  Subtype.ext (map_smul (localHomologyTransport N M E d f).hom (u : R) z.val)

@[simp]
lemma moduleLocalOrientationTransport_neg {x y : FundamentalGroupoid M} (f : x ⟶ y)
    (z : ModuleLocalOrientation N M x.as d) :
    moduleLocalOrientationTransport N M E d f (-z) =
      -moduleLocalOrientationTransport N M E d f z :=
  Subtype.ext (map_neg (localHomologyTransport N M E d f).hom z.val)

end Transport

end TauCeti

namespace Topology.IsOpenEmbedding

open TauCeti

variable {M M' : Type w} [TopologicalSpace M] [TopologicalSpace M'] [T1Space M'] {j : M → M'}
  {R : Type u} [Ring R]

/-- An open embedding `j : M → M'` into a `T₁` space identifies the local `N`-orientations of `M`
at `x` with those of `M'` at `j x`, through the excision isomorphism on local homology. -/
def moduleLocalOrientationEquiv (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M) (d : ℕ) :
    ModuleLocalOrientation N M x d ≃ ModuleLocalOrientation N M' (j x) d :=
  let e := localHomologyIsoOfIsOpenEmbedding N hj x d
  e.toLinearEquiv.toEquiv.subtypeEquiv fun z ↦
    ⟨fun hz ↦ hz.map e, fun hz ↦ (e.hom_inv_id_apply z) ▸ hz.map e.symm⟩

@[simp]
lemma coe_moduleLocalOrientationEquiv (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M)
    {d : ℕ} (z : ModuleLocalOrientation N M x d) :
    (hj.moduleLocalOrientationEquiv N x d z).val =
      (localHomologyIsoOfIsOpenEmbedding N hj x d).hom z.val :=
  (rfl)

@[simp]
lemma coe_moduleLocalOrientationEquiv_symm (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M)
    {d : ℕ} (z : ModuleLocalOrientation N M' (j x) d) :
    ((hj.moduleLocalOrientationEquiv N x d).symm z).val =
      (localHomologyIsoOfIsOpenEmbedding N hj x d).inv z.val :=
  (rfl)

/-- The map of local homology induced by `j` carries the local `N`-orientation at `x` corresponding
to `z` at `j x` back to `z`. -/
lemma localHomologyMap_moduleLocalOrientationEquiv_symm (hj : IsOpenEmbedding j)
    (N : ModuleCat.{w} R) (x : M) {d : ℕ} (z : ModuleLocalOrientation N M' (j x) d)
    (h : j ⁻¹' {j x} ⊆ {x}) :
    localHomologyMap N ⟨j, hj.continuous⟩ h d
      ((hj.moduleLocalOrientationEquiv N x d).symm z).val = z.val := by
  have h' := (localHomologyIsoOfIsOpenEmbedding N hj x d).inv_hom_id_apply z.val
  rwa [localHomologyIsoOfIsOpenEmbedding_hom, ← coe_moduleLocalOrientationEquiv_symm] at h'

@[simp]
lemma moduleLocalOrientationEquiv_smul (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M)
    {d : ℕ} (u : Rˣ) (z : ModuleLocalOrientation N M x d) :
    hj.moduleLocalOrientationEquiv N x d (u • z) =
      u • hj.moduleLocalOrientationEquiv N x d z :=
  Subtype.ext (map_smul (localHomologyIsoOfIsOpenEmbedding N hj x d).hom.hom (u : R) z.val)

@[simp]
lemma moduleLocalOrientationEquiv_neg (hj : IsOpenEmbedding j) (N : ModuleCat.{w} R) (x : M)
    {d : ℕ} (z : ModuleLocalOrientation N M x d) :
    hj.moduleLocalOrientationEquiv N x d (-z) = -hj.moduleLocalOrientationEquiv N x d z :=
  Subtype.ext (map_neg (localHomologyIsoOfIsOpenEmbedding N hj x d).hom.hom z.val)

@[simp]
lemma moduleLocalOrientationEquiv_id [T1Space M] (N : ModuleCat.{w} R) (x : M) (d : ℕ) :
    IsOpenEmbedding.id.moduleLocalOrientationEquiv N x d = Equiv.refl _ :=
  Equiv.ext fun z ↦ Subtype.ext <| by
    rw [coe_moduleLocalOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_id]
    rfl

@[simp]
lemma moduleLocalOrientationEquiv_trans {M'' : Type w} [TopologicalSpace M''] [T1Space M'']
    {j' : M' → M''} (hj : IsOpenEmbedding j) (hj' : IsOpenEmbedding j') (N : ModuleCat.{w} R)
    (x : M) (d : ℕ) :
    (hj.moduleLocalOrientationEquiv N x d).trans (hj'.moduleLocalOrientationEquiv N (j x) d) =
      (hj'.comp hj).moduleLocalOrientationEquiv N x d :=
  Equiv.ext fun z ↦ Subtype.ext <| by
    rw [Equiv.trans_apply, coe_moduleLocalOrientationEquiv, coe_moduleLocalOrientationEquiv,
      coe_moduleLocalOrientationEquiv, ← ConcreteCategory.comp_apply, ← Iso.trans_hom,
      localHomologyIsoOfIsOpenEmbedding_trans]

end Topology.IsOpenEmbedding

namespace TauCeti

/-- An *`N`-orientation* of `M` in degree `d`: a choice of local `N`-orientation at each point of
`M` that is invariant under transport along path classes. For `N = R` and `d = finrank ℝ E`, this is
an `R`-orientation of the topological manifold `M` in the sense of Hatcher, Section 3.3. -/
structure ModuleOrientation {R : Type u} [Ring R] (N : ModuleCat.{w} R) (M E : Type w)
    [TopologicalSpace M] [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E M] (d : ℕ) where
  /-- The local `N`-orientation at each point of `M`. -/
  toFun (x : M) : ModuleLocalOrientation N M x d
  /-- Transport along any path class carries the local orientation at its start to that at its
  end. -/
  moduleLocalOrientationTransport_toFun' {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    moduleLocalOrientationTransport N M E d f (toFun x.as) = toFun y.as

namespace ModuleOrientation

section General

variable {R : Type u} [Ring R] {N : ModuleCat.{w} R}
  {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {d : ℕ}

instance : DFunLike (ModuleOrientation N M E d) M (fun x ↦ ModuleLocalOrientation N M x d) where
  coe := toFun
  coe_injective o o' h := by
    cases o
    cases o'
    congr

@[simp]
theorem toFun_eq_coe (o : ModuleOrientation N M E d) : o.toFun = o :=
  (rfl)

@[simp]
theorem coe_mk (o : ∀ x : M, ModuleLocalOrientation N M x d)
    (h : ∀ {x y : FundamentalGroupoid M} (f : x ⟶ y),
      moduleLocalOrientationTransport N M E d f (o x.as) = o y.as) :
    ⇑(⟨o, h⟩ : ModuleOrientation N M E d) = o :=
  (rfl)

@[ext]
theorem ext {o o' : ModuleOrientation N M E d} (h : ∀ x, o x = o' x) : o = o' :=
  DFunLike.ext _ _ h

@[simp]
theorem moduleLocalOrientationTransport_apply (o : ModuleOrientation N M E d)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    moduleLocalOrientationTransport N M E d f (o x.as) = o y.as :=
  o.moduleLocalOrientationTransport_toFun' f

/-- On local homology classes, `o` is invariant under `TauCeti.localHomologyTransport`. -/
theorem localHomologyTransport_coe_apply (o : ModuleOrientation N M E d)
    {x y : FundamentalGroupoid M} (f : x ⟶ y) :
    localHomologyTransport N M E d f (o x.as).val = (o y.as).val := by
  rw [← coe_moduleLocalOrientationTransport, moduleLocalOrientationTransport_apply]

instance : MulAction Rˣ (ModuleOrientation N M E d) where
  smul u o := ⟨fun x ↦ u • o x, fun f ↦ by
    rw [moduleLocalOrientationTransport_smul, moduleLocalOrientationTransport_apply]⟩
  one_smul o := ext fun x ↦ one_smul Rˣ (o x)
  mul_smul u v o := ext fun x ↦ mul_smul u v (o x)

@[simp]
theorem smul_apply (u : Rˣ) (o : ModuleOrientation N M E d) (x : M) : (u • o) x = u • o x :=
  (rfl)

instance : InvolutiveNeg (ModuleOrientation N M E d) where
  neg o := ⟨fun x ↦ -o x, fun f ↦ by
    rw [moduleLocalOrientationTransport_neg, moduleLocalOrientationTransport_apply]⟩
  neg_neg o := ext fun x ↦ neg_neg (o x)

@[simp]
theorem neg_apply (o : ModuleOrientation N M E d) (x : M) : (-o) x = -o x :=
  (rfl)

/-- An isomorphism of coefficient modules `e : N ≅ N'` induces an equivalence between
`N`-orientations and `N'`-orientations. -/
def equivOfCoefficientsIso {N' : ModuleCat.{w} R} (e : N ≅ N') :
    ModuleOrientation N M E d ≃ ModuleOrientation N' M E d where
  toFun o :=
    { toFun x := ModuleLocalOrientation.equivOfCoefficientsIso e x d (o x)
      moduleLocalOrientationTransport_toFun' {x y} f := Subtype.ext <| by
        have h := ConcreteCategory.congr_hom
          (localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom (E := E) e d f)
          (o x.as).val
        simpa [o.localHomologyTransport_coe_apply f] using h.symm }
  invFun o :=
    { toFun x := (ModuleLocalOrientation.equivOfCoefficientsIso e x d).symm (o x)
      moduleLocalOrientationTransport_toFun' {x y} f := by
        apply (ModuleLocalOrientation.equivOfCoefficientsIso e y.as d).injective
        rw [Equiv.apply_symm_apply]
        apply Subtype.ext
        have h : (localHomologyIsoOfCoefficientsIso e ({y.as} : Set M) d).hom
            (localHomologyTransport N M E d f
              ((ModuleLocalOrientation.equivOfCoefficientsIso e x.as d).symm (o x.as)).val) =
            localHomologyTransport N' M E d f
              ((localHomologyIsoOfCoefficientsIso e ({x.as} : Set M) d).hom
                ((ModuleLocalOrientation.equivOfCoefficientsIso e x.as d).symm (o x.as)).val) :=
          (ConcreteCategory.comp_apply _ _ _).symm.trans
            ((ConcreteCategory.congr_hom
              (localHomologyTransport_comp_localHomologyIsoOfCoefficientsIso_hom (E := E) e d f)
              _).trans (ConcreteCategory.comp_apply _ _ _))
        rw [ModuleLocalOrientation.coe_equivOfCoefficientsIso,
          coe_moduleLocalOrientationTransport, h,
          ← ModuleLocalOrientation.coe_equivOfCoefficientsIso, Equiv.apply_symm_apply,
          o.localHomologyTransport_coe_apply] }
  left_inv o := ext fun x ↦ (ModuleLocalOrientation.equivOfCoefficientsIso e x d).symm_apply_apply _
  right_inv o := ext fun x ↦
    (ModuleLocalOrientation.equivOfCoefficientsIso e x d).apply_symm_apply _

/-- With integral coefficients `ULift ℤ`, `TauCeti.ModuleOrientation` is canonically equivalent to
`TauCeti.HomologicalOrientation`. -/
def equivHomologicalOrientation :
    ModuleOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d ≃ HomologicalOrientation M E d where
  toFun o :=
    { toFun x := ModuleLocalOrientation.equivLocalOrientation M x d (o x)
      localOrientationTransport_toFun' f := Subtype.ext <| by
        rw [coe_localOrientationTransport, ModuleLocalOrientation.coe_equivLocalOrientation,
          ModuleLocalOrientation.coe_equivLocalOrientation, o.localHomologyTransport_coe_apply] }
  invFun o :=
    { toFun x := (ModuleLocalOrientation.equivLocalOrientation M x d).symm (o x)
      moduleLocalOrientationTransport_toFun' f := Subtype.ext <| by
        rw [coe_moduleLocalOrientationTransport,
          ModuleLocalOrientation.coe_equivLocalOrientation_symm,
          ModuleLocalOrientation.coe_equivLocalOrientation_symm, ← coe_localOrientationTransport,
          o.localOrientationTransport_apply] }
  left_inv o := ext fun _ ↦ (ModuleLocalOrientation.equivLocalOrientation M _ d).symm_apply_apply _
  right_inv o := HomologicalOrientation.ext fun _ ↦
    (ModuleLocalOrientation.equivLocalOrientation M _ d).apply_symm_apply _

@[simp]
theorem coe_equivHomologicalOrientation_apply
    (o : ModuleOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d) (x : M) :
    (equivHomologicalOrientation o x).val = (o x).val :=
  (rfl)

@[simp]
theorem coe_equivHomologicalOrientation_symm_apply (o : HomologicalOrientation M E d) (x : M) :
    (equivHomologicalOrientation.symm o x).val = (o x).val :=
  (rfl)

@[simp]
theorem equivHomologicalOrientation_neg
    (o : ModuleOrientation (ModuleCat.of ℤ (ULift.{w} ℤ)) M E d) :
    equivHomologicalOrientation (-o) = -equivHomologicalOrientation o :=
  HomologicalOrientation.ext fun _ ↦ Subtype.ext rfl

/-- **An `N`-orientation of a connected manifold is determined by its value at one point.** -/
theorem eq_of_apply_eq [ConnectedSpace M] {o o' : ModuleOrientation N M E d} {x : M}
    (h : o x = o' x) : o = o' := by
  have := ChartedSpace.locallyPathConnectedSpace E M
  have := PathConnectedSpace.of_locallyPathConnectedSpace (X := M)
  refine ext fun y ↦ ?_
  let f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y)
  have hf := congrArg (moduleLocalOrientationTransport N M E d f) h
  rwa [moduleLocalOrientationTransport_apply, moduleLocalOrientationTransport_apply] at hf

/-- On a connected `n`-manifold over a Dedekind-finite ring `R`, any two `R`-orientations differ by
a unit of `R`. -/
theorem exists_units_smul_eq {R : Type w} [Ring R] [IsDedekindFiniteMonoid R] [ConnectedSpace M]
    (hd : finrank ℝ E = d) (o o' : ModuleOrientation (ModuleCat.of R R) M E d) :
    ∃ u : Rˣ, u • o = o' := by
  subst hd
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := M)
  obtain ⟨u, hu⟩ := ModuleLocalOrientation.exists_units_smul_eq_of_iso
    (singularHomologyComplSingletonFinrankIso (ModuleCat.of R R) (chartAt E x)
      (mem_chart_source E x))
    (o x) (o' x)
  exact ⟨u, eq_of_apply_eq (x := x) hu⟩

/-- On a nonempty `n`-manifold with faithful coefficients over a commutative ring `R`, `Rˣ` acts
freely on `N`-orientations. -/
theorem units_smul_injective {R : Type u} [CommRing R] {N : ModuleCat.{w} R} [FaithfulSMul R N]
    [Nonempty M] (hd : finrank ℝ E = d) (o : ModuleOrientation N M E d) :
    Function.Injective fun u : Rˣ ↦ u • o := by
  obtain ⟨x⟩ := ‹Nonempty M›
  intro u v huv
  exact (o x).units_smul_injective hd (DFunLike.congr_fun huv x)

section SimplyConnected

variable [SimplyConnectedSpace M]

/-- **Orientations of a simply connected manifold.** A local `N`-orientation at one point extends
by path transport to an `N`-orientation of `M`. -/
def ofSimplyConnectedSpace (x : M) (z : ModuleLocalOrientation N M x d) :
    ModuleOrientation N M E d where
  toFun y := moduleLocalOrientationTransport N M E d
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y) :
      FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) z
  moduleLocalOrientationTransport_toFun' f := by
    rw [← Equiv.trans_apply, ← moduleLocalOrientationTransport_comp]
    exact congrArg (moduleLocalOrientationTransport N M E d · z)
      (Subsingleton.elim (α := Path.Homotopic.Quotient x _) _ _)

theorem ofSimplyConnectedSpace_apply (x : M) (z : ModuleLocalOrientation N M x d) (y : M)
    (f : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ofSimplyConnectedSpace (E := E) x z y = moduleLocalOrientationTransport N M E d f z :=
  congrArg (moduleLocalOrientationTransport N M E d · z)
    (Subsingleton.elim (α := Path.Homotopic.Quotient x y) _ _)

@[simp]
theorem ofSimplyConnectedSpace_apply_self (x : M) (z : ModuleLocalOrientation N M x d) :
    ofSimplyConnectedSpace (E := E) x z x = z := by
  rw [ofSimplyConnectedSpace_apply x z x (𝟙 _), moduleLocalOrientationTransport_id,
    Equiv.refl_apply]

/-- Every simply connected `n`-manifold has an `R`-orientation over any ring `R`. -/
theorem nonempty_of_simplyConnectedSpace {R : Type w} [Ring R] (hd : finrank ℝ E = d) :
    Nonempty (ModuleOrientation (ModuleCat.of R R) M E d) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  exact ⟨ofSimplyConnectedSpace x (ModuleLocalOrientation.nonempty_of_finrank_eq x hd).some⟩

end SimplyConnected

section OpenEmbedding

variable {M' M'' : Type w} [TopologicalSpace M'] [T2Space M'] [TopologicalSpace M''] [T2Space M'']
  [ChartedSpace E M'] [ChartedSpace E M''] {j : M → M'}

/-- The **pullback of an `N`-orientation along an open embedding** `j : M → M'`. -/
def comap (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j) :
    ModuleOrientation N M E d where
  toFun x := (hj.moduleLocalOrientationEquiv N x d).symm (o (j x))
  moduleLocalOrientationTransport_toFun' {x y} f := by
    apply (hj.moduleLocalOrientationEquiv N y.as d).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    -- Elementwise, excision along `j` intertwines the local homology transports of `M` and `M'`.
    have h : (localHomologyIsoOfIsOpenEmbedding N hj y.as d).hom
        (localHomologyTransport N M E d f
          ((hj.moduleLocalOrientationEquiv N x.as d).symm (o (j x.as))).val) =
        localHomologyTransport N M' E d
          ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f)
          ((localHomologyIsoOfIsOpenEmbedding N hj x.as d).hom
            ((hj.moduleLocalOrientationEquiv N x.as d).symm (o (j x.as))).val) :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom
          (localHomologyTransport_comp_localHomologyIsoOfIsOpenEmbedding_hom N (E := E) hj d f)
          _).trans (ConcreteCategory.comp_apply _ _ _))
    rw [IsOpenEmbedding.coe_moduleLocalOrientationEquiv, coe_moduleLocalOrientationTransport, h,
      ← IsOpenEmbedding.coe_moduleLocalOrientationEquiv, Equiv.apply_symm_apply]
    exact o.localHomologyTransport_coe_apply ((FundamentalGroupoid.map ⟨j, hj.continuous⟩).map f)

lemma comap_apply (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j) (x : M) :
    o.comap hj x = (hj.moduleLocalOrientationEquiv N x d).symm (o (j x)) :=
  (rfl)

@[simp]
lemma moduleLocalOrientationEquiv_comap_apply (o : ModuleOrientation N M' E d)
    (hj : IsOpenEmbedding j) (x : M) :
    hj.moduleLocalOrientationEquiv N x d (o.comap hj x) = o (j x) :=
  Equiv.apply_symm_apply _ _

lemma comap_congr (o : ModuleOrientation N M' E d) {j' : M → M'} (hj : IsOpenEmbedding j)
    (hj' : IsOpenEmbedding j') (hjj' : j = j') : o.comap hj = o.comap hj' := by
  subst hjj'
  rfl

@[simp]
lemma comap_smul (u : Rˣ) (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j) :
    (u • o).comap hj = u • o.comap hj := by
  ext x : 1
  apply (hj.moduleLocalOrientationEquiv N x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply, smul_apply, smul_apply,
    IsOpenEmbedding.moduleLocalOrientationEquiv_smul, moduleLocalOrientationEquiv_comap_apply]

@[simp]
lemma comap_neg (o : ModuleOrientation N M' E d) (hj : IsOpenEmbedding j) :
    (-o).comap hj = -o.comap hj := by
  ext x : 1
  apply (hj.moduleLocalOrientationEquiv N x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply, neg_apply, neg_apply,
    IsOpenEmbedding.moduleLocalOrientationEquiv_neg, moduleLocalOrientationEquiv_comap_apply]

@[simp]
lemma comap_id (o : ModuleOrientation N M E d) : o.comap IsOpenEmbedding.id = o := by
  ext x : 1
  apply (IsOpenEmbedding.id.moduleLocalOrientationEquiv N x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply, IsOpenEmbedding.moduleLocalOrientationEquiv_id]
  rfl

lemma comap_comap (o : ModuleOrientation N M'' E d) {j' : M' → M''} (hj' : IsOpenEmbedding j')
    (hj : IsOpenEmbedding j) : (o.comap hj').comap hj = o.comap (hj'.comp hj) := by
  ext x : 1
  apply ((hj'.comp hj).moduleLocalOrientationEquiv N x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply, ← IsOpenEmbedding.moduleLocalOrientationEquiv_trans
    hj hj', Equiv.trans_apply, moduleLocalOrientationEquiv_comap_apply,
    moduleLocalOrientationEquiv_comap_apply]
  rfl

@[simp]
lemma comap_symm_comap (o : ModuleOrientation N M' E d) (e : M ≃ₜ M') :
    (o.comap e.isOpenEmbedding).comap e.symm.isOpenEmbedding = o := by
  rw [comap_comap, o.comap_congr _ IsOpenEmbedding.id (funext e.apply_symm_apply), comap_id]

end OpenEmbedding

end General

end ModuleOrientation

section ExtendScalars

variable {R S : Type w} [CommRing R] [CommRing S] (f : R →+* S)
  [PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} f)]

/-- Exact extension of scalars along `f : R →+* S` carries a local `R`-orientation `z` to a local
`S`-orientation `(localHomologyExtendScalarsIso f {x} d).hom (1 ⊗ₜ z)`. -/
theorem IsModuleLocalOrientation.extendScalars {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    {z : (localHomology (ModuleCat.of R R) ({x} : Set M) d : ModuleCat.{w} R)}
    (hz : IsModuleLocalOrientation (ModuleCat.of R R) x d z) :
    IsModuleLocalOrientation (ModuleCat.of S S) x d
      ((localHomologyExtendScalarsIso f ({x} : Set M) d).hom ((1 : S) ⊗ₜ[R, f] z)) := by
  -- `1 ↦ z` is surjective by `hz`, hence an epimorphism; left-adjointness of `extendScalars f`
  -- preserves epimorphisms, so `1 ↦ 1 ⊗ₜ z` is surjective onto `S ⊗[R] H_d(M, M ∖ {x}; R)`.
  let P := localHomology (A := ModuleCat.{w} R) (ModuleCat.of R R) ({x} : Set M) d
  let φ : ModuleCat.of R R ⟶ P := ModuleCat.ofHom (LinearMap.toSpanSingleton R P z)
  have hφ : Function.Surjective φ :=
    LinearMap.range_eq_top.1 ((LinearMap.span_singleton_eq_range R P z).symm.trans hz)
  have : Epi φ := (ModuleCat.epi_iff_surjective φ).2 hφ
  let ψ : ModuleCat.of S S ⟶ (ModuleCat.extendScalars.{w, w, w} f).obj P :=
    (extendScalarsSelfIso f).inv ≫ (ModuleCat.extendScalars.{w, w, w} f).map φ
  have hψ : Function.Surjective ψ := (ModuleCat.epi_iff_surjective ψ).1 inferInstance
  let η := (ModuleCat.extendRestrictScalarsAdj.{w, w, w} f).unit
  let t1 : (ModuleCat.extendScalars.{w, w, w} f).obj (ModuleCat.of R R) :=
    η.app (ModuleCat.of R R) (1 : R)
  let tz : (ModuleCat.extendScalars.{w, w, w} f).obj P := η.app P z
  have hψ1 : ψ (1 : S) = tz := by
    have hinv : (extendScalarsSelfIso f).inv (1 : S) = t1 := extendScalarsSelfIso_inv_apply f 1
    have hnat : ((ModuleCat.extendScalars.{w, w, w} f).map φ) t1 = η.app P (φ (1 : R)) :=
      ConcreteCategory.congr_hom (η.naturality φ).symm (1 : R)
    exact (ConcreteCategory.comp_apply (extendScalarsSelfIso f).inv
      ((ModuleCat.extendScalars.{w, w, w} f).map φ) (1 : S)).trans
      ((congrArg ((ModuleCat.extendScalars.{w, w, w} f).map φ) hinv).trans
        (hnat.trans (congrArg (η.app P) (one_smul R z))))
  refine (ModuleCat.span_singleton_apply_eq_top_iff
    (localHomologyExtendScalarsIso f ({x} : Set M) d).hom).2 ?_
  have htz : Submodule.span S {tz} = ⊤ := by
    rw [← hψ1, Submodule.span_singleton_eq_top_iff]
    intro y
    obtain ⟨s, rfl⟩ := hψ y
    refine ⟨s, ?_⟩
    rw [← map_smul ψ.hom s (1 : S), smul_eq_mul, mul_one]
  exact (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{w, w, w} f P z) ▸ htz

/-- Exact extension of scalars along `f : R →+* S` on local `R`-orientations. -/
def ModuleLocalOrientation.extendScalars {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (z : ModuleLocalOrientation (ModuleCat.of R R) M x d) :
    ModuleLocalOrientation (ModuleCat.of S S) M x d :=
  ⟨(localHomologyExtendScalarsIso f ({x} : Set M) d).hom ((1 : S) ⊗ₜ[R, f] z.val),
    z.property.extendScalars f⟩

@[simp]
lemma ModuleLocalOrientation.coe_extendScalars {M : Type w} [TopologicalSpace M] {x : M} {d : ℕ}
    (z : ModuleLocalOrientation (ModuleCat.of R R) M x d) :
    (z.extendScalars f).val =
      (localHomologyExtendScalarsIso f ({x} : Set M) d).hom ((1 : S) ⊗ₜ[R, f] z.val) :=
  (rfl)

namespace ModuleOrientation

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {d : ℕ}

/-- **Extension of scalars of an `R`-orientation** along a ring homomorphism `f : R →+* S` whose
extension of scalars preserves finite limits (for instance any flat ring homomorphism). -/
def extendScalars (o : ModuleOrientation (ModuleCat.of R R) M E d) :
    ModuleOrientation (ModuleCat.of S S) M E d where
  toFun x := (o x).extendScalars f
  moduleLocalOrientationTransport_toFun' {x y} g := Subtype.ext <| by
    let η := (ModuleCat.extendRestrictScalarsAdj.{w, w, w} f).unit
    let tx : (ModuleCat.extendScalars.{w, w, w} f).obj
        (localHomology (ModuleCat.of R R) ({x.as} : Set M) d) := η.app _ (o x.as).val
    let ty : (ModuleCat.extendScalars.{w, w, w} f).obj
        (localHomology (ModuleCat.of R R) ({y.as} : Set M) d) := η.app _ (o y.as).val
    have hcomm :
        localHomologyTransport (ModuleCat.of S S) M E d g
          ((localHomologyExtendScalarsIso f ({x.as} : Set M) d).hom tx) =
        (localHomologyExtendScalarsIso f ({y.as} : Set M) d).hom
          (((ModuleCat.extendScalars.{w, w, w} f).map
            (localHomologyTransport (ModuleCat.of R R) M E d g)) tx) :=
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom
          (map_localHomologyTransport_comp_localHomologyExtendScalarsIso_hom (E := E) f d g).symm
          tx).trans (ConcreteCategory.comp_apply _ _ _))
    have hnat :
        ((ModuleCat.extendScalars.{w, w, w} f).map
            (localHomologyTransport (ModuleCat.of R R) M E d g)) tx = ty :=
      (ConcreteCategory.congr_hom
        (η.naturality (localHomologyTransport (ModuleCat.of R R) M E d g)).symm (o x.as).val).trans
        (congrArg (η.app _) (o.localHomologyTransport_coe_apply g))
    exact hcomm.trans (congrArg (localHomologyExtendScalarsIso f ({y.as} : Set M) d).hom hnat)

@[simp]
lemma extendScalars_apply (o : ModuleOrientation (ModuleCat.of R R) M E d) (x : M) :
    o.extendScalars f x = (o x).extendScalars f :=
  (rfl)

lemma coe_extendScalars_apply (o : ModuleOrientation (ModuleCat.of R R) M E d) (x : M) :
    (o.extendScalars f x).val =
      (localHomologyExtendScalarsIso f ({x} : Set M) d).hom ((1 : S) ⊗ₜ[R, f] (o x).val) :=
  (rfl)

@[simp]
lemma extendScalars_smul (u : Rˣ) (o : ModuleOrientation (ModuleCat.of R R) M E d) :
    (u • o).extendScalars f = Units.map f.toMonoidHom u • o.extendScalars f := by
  ext x : 1
  apply Subtype.ext
  let P := localHomology (A := ModuleCat.{w} R) (ModuleCat.of R R) ({x} : Set M) d
  let η := (ModuleCat.extendRestrictScalarsAdj.{w, w, w} f).unit.app P
  let tx : (ModuleCat.extendScalars.{w, w, w} f).obj P := η (o x).val
  let tux : (ModuleCat.extendScalars.{w, w, w} f).obj P := η ((u : R) • (o x).val)
  have hsmul : tux = (f u : S) • tx := map_smul η.hom (u : R) (o x).val
  exact (congrArg (localHomologyExtendScalarsIso f ({x} : Set M) d).hom hsmul).trans
    (map_smul (localHomologyExtendScalarsIso f ({x} : Set M) d).hom.hom (f u : S) tx)

/-- Extension of scalars commutes with pullback along open embeddings. -/
lemma comap_extendScalars {M' : Type w} [TopologicalSpace M'] [T2Space M'] [ChartedSpace E M']
    (o : ModuleOrientation (ModuleCat.of R R) M' E d) {j : M → M'} (hj : IsOpenEmbedding j) :
    (o.extendScalars f).comap hj = (o.comap hj).extendScalars f := by
  ext x : 1
  apply (hj.moduleLocalOrientationEquiv (ModuleCat.of S S) x d).injective
  rw [moduleLocalOrientationEquiv_comap_apply]
  apply Subtype.ext
  have hjx : (⟨j, hj.continuous⟩ : C(M, M')) ⁻¹' {j x} ⊆ {x} := fun _ hy ↦ hj.injective hy
  have hmap : localHomologyMap (ModuleCat.of R R) ⟨j, hj.continuous⟩ hjx d (o.comap hj x).val =
      (o (j x)).val :=
    hj.localHomologyMap_moduleLocalOrientationEquiv_symm (ModuleCat.of R R) x (o (j x)) hjx
  let η := (ModuleCat.extendRestrictScalarsAdj.{w, w, w} f).unit
  let tx : (ModuleCat.extendScalars.{w, w, w} f).obj
      (localHomology (ModuleCat.of R R) ({x} : Set M) d) := η.app _ (o.comap hj x).val
  let tjx : (ModuleCat.extendScalars.{w, w, w} f).obj
      (localHomology (ModuleCat.of R R) ({j x} : Set M') d) := η.app _ (o (j x)).val
  have hcomm :
      localHomologyMap (ModuleCat.of S S) ⟨j, hj.continuous⟩ hjx d
        ((localHomologyExtendScalarsIso f ({x} : Set M) d).hom tx) =
      (localHomologyExtendScalarsIso f ({j x} : Set M') d).hom
        (((ModuleCat.extendScalars.{w, w, w} f).map
          (localHomologyMap (ModuleCat.of R R) ⟨j, hj.continuous⟩ hjx d)) tx) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      ((ConcreteCategory.congr_hom
        (map_localHomologyMap_comp_localHomologyExtendScalarsIso_hom f ⟨j, hj.continuous⟩ hjx
          d).symm tx).trans (ConcreteCategory.comp_apply _ _ _))
  have hnat :
      ((ModuleCat.extendScalars.{w, w, w} f).map
          (localHomologyMap (ModuleCat.of R R) ⟨j, hj.continuous⟩ hjx d)) tx = tjx :=
    (ConcreteCategory.congr_hom
      (η.naturality (localHomologyMap (ModuleCat.of R R) ⟨j, hj.continuous⟩ hjx d)).symm
      (o.comap hj x).val).trans (congrArg (η.app _) hmap)
  rw [IsOpenEmbedding.coe_moduleLocalOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom]
  exact (hcomm.trans (congrArg (localHomologyExtendScalarsIso f ({j x} : Set M') d).hom hnat)).symm

end ModuleOrientation

end ExtendScalars

namespace ModuleOrientation

section Canonical

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [ChartedSpace E M]
  {n : ℕ}

/-- **Canonical `K`-orientation when `1` is the only unit of `K`.** Every point of an `n`-manifold
has a unique local `K`-orientation, and path transport is forced to preserve it. -/
def ofSubsingletonUnits {K : Type w} [CommRing K] [Subsingleton Kˣ] (hn : finrank ℝ E = n) :
    ModuleOrientation (ModuleCat.of K K) M E n where
  toFun x := (ModuleLocalOrientation.uniqueOfSubsingletonUnits x hn).default
  moduleLocalOrientationTransport_toFun' {_ y} _ :=
    haveI := ModuleLocalOrientation.uniqueOfSubsingletonUnits (M := M) (E := E) (K := K) y.as hn
    Subsingleton.elim _ _

/-- When `1` is the only unit of a commutative ring `K`, every topological `n`-manifold has a
unique `K`-orientation. -/
@[instance_reducible]
def uniqueOfSubsingletonUnits {K : Type w} [CommRing K] [Subsingleton Kˣ] (hn : finrank ℝ E = n) :
    Unique (ModuleOrientation (ModuleCat.of K K) M E n) where
  default := ofSubsingletonUnits hn
  uniq _ := ext fun x ↦
    haveI := ModuleLocalOrientation.uniqueOfSubsingletonUnits (M := M) (E := E) (K := K) x hn
    Subsingleton.elim _ _

private theorem subsingleton_units_ulift_zmod_two : Subsingleton (ULift.{w} (ZMod 2))ˣ :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subsingleton_units_of_natCard_eq_two
    ((Nat.card_congr Equiv.ulift).trans (by simp : Nat.card (ZMod 2) = 2))

private def uliftZModTwoToRing {R : Type w} [CommRing R] (h2 : (2 : R) = 0) :
    ULift.{w} (ZMod 2) →+* R :=
  (ZMod.castHom (ringChar.dvd (by simpa using h2)) R).comp ULift.ringEquiv.toRingHom

private theorem preservesFiniteLimits_extendScalars_uliftZModTwoToRing {R : Type w} [CommRing R]
    (h2 : (2 : R) = 0) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{w, w, w} (uliftZModTwoToRing h2)) :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.Flat.of_isField (Field.toIsField (ULift.{w} (ZMod 2))) (uliftZModTwoToRing h2))

/-- **Every topological `n`-manifold is canonically `R`-orientable when `(2 : R) = 0`**
(Hatcher, Section 3.3, p. 235): the unique `ULift (ZMod 2)`-orientation extends along the flat
canonical map `ULift (ZMod 2) →+* R`. -/
def ofTwoEqZero {R : Type w} [CommRing R] (hn : finrank ℝ E = n) (h2 : (2 : R) = 0) :
    ModuleOrientation (ModuleCat.of R R) M E n :=
  letI := subsingleton_units_ulift_zmod_two.{w}
  letI := preservesFiniteLimits_extendScalars_uliftZModTwoToRing h2
  (ofSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn).extendScalars
    (uliftZModTwoToRing h2)

/-- The canonical `R`-orientation for `(2 : R) = 0` pulls back to itself along open embeddings. -/
@[simp]
theorem comap_ofTwoEqZero {M' : Type w} [TopologicalSpace M'] [T2Space M'] [ChartedSpace E M']
    {R : Type w} [CommRing R] (hn : finrank ℝ E = n) (h2 : (2 : R) = 0) {j : M → M'}
    (hj : IsOpenEmbedding j) :
    (ofTwoEqZero (M := M') hn h2).comap hj = ofTwoEqZero (M := M) hn h2 := by
  dsimp [ofTwoEqZero]
  have := subsingleton_units_ulift_zmod_two.{w}
  have := preservesFiniteLimits_extendScalars_uliftZModTwoToRing h2
  rw [comap_extendScalars]
  congr 1
  have := uniqueOfSubsingletonUnits (M := M) (E := E) (K := ULift.{w} (ZMod 2)) hn
  exact Subsingleton.elim _ _

end Canonical

end ModuleOrientation

end TauCeti
