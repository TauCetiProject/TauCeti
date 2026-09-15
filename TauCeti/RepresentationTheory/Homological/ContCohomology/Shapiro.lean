/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Homogeneous

/-!
# Shapiro's lemma in degrees zero, one and two

For a profinite group `G`, a **closed** subgroup `U` and a discrete `U`-module `A`, the coinduced
module `Coind_U^G A` of `TauCeti.DiscreteCoind` computes the cohomology of `U`:

```text
H⁰(G, Coind_U^G A) ≅ H⁰(U, A),   H¹(G, Coind_U^G A) ≅ H¹(U, A),
H²(G, Coind_U^G A) ≅ H²(U, A).
```

All three isomorphisms are *evaluation at `1`* composed with restriction to `U`, so in degrees one
and two the forward map is the compatible-pair pullback `TauCeti.ContCohomology.explicitMap1`,
respectively `explicitMap2`, along the pair consisting of the inclusion `U ↪ G` and the counit
`TauCeti.DiscreteCoind.eval`; nothing about it
depends on a choice. The choice enters only in proving that this map is bijective, and what it uses
is a continuous section of `G → G ⧸ U`
(`TauCeti.exists_continuous_rightCosetFactorization`, Ribes-Zalesskii Prop. 2.2.2): writing
`g = w g * r g` with `w : G → U` continuous and `w (u * g) = u * w g`, a continuous `1`-cocycle
`c` of `U` is spread over `G` as

```text
(a g) x = c (w (x * g)) - c (w x),
```

which is `TauCeti.ContCohomology.coindCochain1`. This is a continuous `1`-cocycle of `G` with
values in `Coind_U^G A` whose Shapiro image is `c` up to the explicit coboundary `d⁰ (c (w 1))`
(`TauCeti.ContCohomology.shapiroCocycles1_coindCocycle1`), and conversely every continuous
`1`-cocycle `f` of `G` differs from the cochain rebuilt from its Shapiro image by an explicit
coboundary (`TauCeti.ContCohomology.sub_coindCochain1_mem_B1`). Those two identities make the
forward map bijective, and because the isomorphism is pinned by its forward direction the section
formula for the inverse (`TauCeti.ContCohomology.explicitShapiro1_symm_apply`) holds for *every*
such factorization, so there is no separate independence statement to prove.

Degree two is the same argument written in the homogeneous form of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Homogeneous.lean`, which is what makes it
manageable: `TauCeti.ContCohomology.coindCochain2` sends a continuous `2`-cocycle `c` of `U` to

```text
(a (g, h)) y = homogeneous2 c (w y) (w (y * g)) (w (y * g * h)),
```

the homogeneous form of `c` read at the three points `y`, `y g`, `y g h` of `G` pushed into `U` by
`w`. Its cocycle identity is the four-term homogeneous relation
`TauCeti.ContCohomology.homogeneous2_add_eq_add`, and the comparison of a cocycle with the cochain
rebuilt from its Shapiro image is the pointwise prism identity
`TauCeti.ContCohomology.homogeneous2_sub_comp` applied along `w`. Here the factorization is
required to be
**normalized**, `w 1 = 1`, which `TauCeti.exists_continuous_rightCosetFactorization` supplies: the
Shapiro image of the rebuilt cochain is then `c` on the nose
(`TauCeti.ContCohomology.shapiroCocycles2_coindCocycle2`), where a factorization with `w 1 = s`
would return the conjugate of `c` by `s` instead. Local constancy of both cochains in their group
arguments is uniform local constancy of the underlying function on the compact groups `G × G` and
`G × G × G` (`TauCeti.exists_isOpen_forall_mul_right_eq`).

## Main definitions

* `TauCeti.ContCohomology.constCoind` and `TauCeti.ContCohomology.explicitShapiro0`: the constant
  coinduced element at a `U`-invariant coefficient, and `H⁰(G, Coind_U^G A) ≃+ H⁰(U, A)`.
* `TauCeti.ContCohomology.shapiroCocycles1` and `TauCeti.ContCohomology.explicitShapiroMap1`: the
  forward Shapiro map on continuous `1`-cocycles and on `H¹`.
* `TauCeti.ContCohomology.shapiroLift`, `TauCeti.ContCohomology.coindCochain1` and
  `TauCeti.ContCohomology.coindCocycle1`: the inverse cochain built from a continuous right-coset
  factorization.
* `TauCeti.ContCohomology.explicitShapiro1`: `H¹(G, Coind_U^G A) ≃+ H¹(U, A)`.
* `TauCeti.ContCohomology.shapiroCocycles2` and `TauCeti.ContCohomology.explicitShapiroMap2`: the
  forward Shapiro map on continuous `2`-cocycles and on `H²`.
* `TauCeti.ContCohomology.coindCochain2` and `TauCeti.ContCohomology.coindCocycle2`: the inverse
  cochain in degree two, built from a normalized continuous right-coset factorization.
* `TauCeti.ContCohomology.explicitShapiro2`: `H²(G, Coind_U^G A) ≃+ H²(U, A)`.

## Implementation notes

Degree zero needs no topological hypothesis beyond a continuous multiplication on `G`: a
`G`-invariant element of the coinduced module is constant, and the constant it takes is
`U`-invariant. Degrees one and two are where profiniteness and closedness of `U` are used, through
the continuous factorization; for an *open* `U` the finite transversal `Quotient.out` would already
suffice, but openness is not assumed anywhere here.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.4). Note the
  terminology trap flagged in the footnote on p. 61: NSW writes `Ind` for what is here the
  *coinduced* functor.
* L. Ribes, P. Zalesskii, *Profinite Groups*, Thm. 6.10.5, which uses `Coind` by that name.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section DegreeZero

variable {G : Type u} [Group G] [TopologicalSpace G] {U : Subgroup G}
  {A : Type v} [AddCommGroup A] [DistribMulAction U A]

variable (G) in
/-- The constant function at a `U`-invariant coefficient, as an element of `Coind_U^G A`. It is
the inverse of the degree-zero Shapiro map. -/
def constCoind (a : H0 U A) : DiscreteCoind G U A :=
  DiscreteCoind.mk G U A (fun _ => (a : A)) (IsLocallyConstant.const _)
    (fun u _ => ((FixedPoints.mem_addSubgroup U A (a : A)).1 a.2 u).symm)

@[simp]
theorem constCoind_apply (a : H0 U A) (g : G) : constCoind G a g = (a : A) := (rfl)

variable [ContinuousMul G]

/-- A `G`-invariant element of `Coind_U^G A` is a constant function: right translation moves `1`
to every point of `G`. -/
theorem apply_eq_apply_one_of_mem_H0 (f : H0 G (DiscreteCoind G U A)) (g : G) :
    (f : DiscreteCoind G U A) g = (f : DiscreteCoind G U A) 1 := by
  have h := (FixedPoints.mem_addSubgroup G (DiscreteCoind G U A)
    (f : DiscreteCoind G U A)).1 f.2 g
  calc (f : DiscreteCoind G U A) g
      = (g • (f : DiscreteCoind G U A)) 1 := by rw [DiscreteCoind.coe_smul, one_mul]
    _ = (f : DiscreteCoind G U A) 1 := by rw [h]

/-- The constant coinduced element is `G`-invariant. -/
theorem constCoind_mem_H0 (a : H0 U A) : constCoind G a ∈ H0 G (DiscreteCoind G U A) :=
  (FixedPoints.mem_addSubgroup G (DiscreteCoind G U A) (constCoind G a)).2 fun _ =>
    DiscreteCoind.ext fun _ => by simp

variable (G U A) in
/-- **Shapiro's lemma in degree zero**, `H⁰(G, Coind_U^G A) ≅ H⁰(U, A)`, by evaluation at `1`.

A `G`-invariant element of the coinduced module is constant and the constant it takes is
`U`-invariant; conversely a `U`-invariant `a : A` is `TauCeti.ContCohomology.constCoind`. Only
continuity of the multiplication on `G` is used: neither compactness of `G` nor closedness of `U`
enters in this degree. -/
def explicitShapiro0 : H0 G (DiscreteCoind G U A) ≃+ H0 U A where
  toFun f := ⟨(f : DiscreteCoind G U A) 1, (FixedPoints.mem_addSubgroup U A _).2 fun u => by
    rw [← DiscreteCoind.apply_coe, apply_eq_apply_one_of_mem_H0 f]⟩
  invFun a := ⟨constCoind G a, constCoind_mem_H0 a⟩
  left_inv f := Subtype.ext (DiscreteCoind.ext fun g => by
    rw [constCoind_apply, apply_eq_apply_one_of_mem_H0 f])
  right_inv a := Subtype.ext (constCoind_apply a 1)
  map_add' _ _ := (rfl)

@[simp]
theorem explicitShapiro0_apply (f : H0 G (DiscreteCoind G U A)) :
    (explicitShapiro0 G U A f : A) = (f : DiscreteCoind G U A) 1 := (rfl)

@[simp]
theorem explicitShapiro0_symm_apply (a : H0 U A) :
    ((explicitShapiro0 G U A).symm a : DiscreteCoind G U A) = constCoind G a := (rfl)

end DegreeZero

section Lift

variable {G : Type u} [Group G] {U : Subgroup G} {A : Type v} (w : G → U) (c : U → A)

/-- The `0`-cochain `y ↦ c (w y)` transporting a `1`-cocycle `c` of `U` along a factorization `w`
of `G` over the right cosets of `U`. Its failure of `U`-equivariance is `c` itself
(`TauCeti.ContCohomology.shapiroLift_mul`), which is why its right-translation differences carry a
nonzero class. -/
def shapiroLift : G → A := fun y => c (w y)

@[simp]
theorem shapiroLift_apply (y : G) : shapiroLift w c y = c (w y) := (rfl)

theorem continuous_shapiroLift [TopologicalSpace G] [TopologicalSpace A] (hw : Continuous w)
    (hc : Continuous c) : Continuous (shapiroLift w c) := hc.comp hw

/-- The failure of `U`-equivariance of the lift of a `1`-cocycle is the cocycle itself. -/
theorem shapiroLift_mul [AddCommGroup A] [DistribMulAction U A]
    (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g)
    (hc : groupCohomology.IsCocycle₁ c) (u : U) (y : G) :
    shapiroLift w c ((u : G) * y) = u • shapiroLift w c y + c u := by
  simp only [shapiroLift_apply, hwmul u y, hc u (w y)]

end Lift

section DegreeOne

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]

omit [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] in
/-- Evaluation at `1` is a compatible coefficient map for the inclusion `U ↪ G`: this is the
hypothesis of `TauCeti.ContCohomology.explicitMap1` that the Shapiro map is the instance of. It is
a named theorem rather than an inline use of `TauCeti.DiscreteCoind.eval_smul` because the
inclusion has to be spelled as `ContinuousMonoidHom.subgroupSubtype`. -/
theorem eval_subgroupSubtype_smul (u : U) (f : DiscreteCoind G U A) :
    DiscreteCoind.eval G U A (ContinuousMonoidHom.subgroupSubtype U u • f) =
      u • DiscreteCoind.eval G U A f :=
  DiscreteCoind.eval_smul u f

/-- **The forward Shapiro map on continuous `1`-cocycles**: restrict a continuous `1`-cocycle of
`G` with coefficients in `Coind_U^G A` to `U`, and evaluate its values at `1`. -/
noncomputable abbrev shapiroCocycles1 : Z1 G (DiscreteCoind G U A) →+ Z1 U A :=
  cocyclesMap1 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

omit [CompactSpace G] [ContinuousSMul U A] in
@[simp]
theorem shapiroCocycles1_apply (f : Z1 G (DiscreteCoind G U A)) (u : U) :
    (shapiroCocycles1 G U A f : U → A) u = (f : G → DiscreteCoind G U A) (u : G) 1 := by
  simp [cocyclesMap1_apply]

/-- **The forward Shapiro map on `H¹`**, the compatible-pair pullback along the inclusion `U ↪ G`
and evaluation at `1`. `TauCeti.ContCohomology.explicitShapiro1` upgrades it to an isomorphism. -/
noncomputable abbrev explicitShapiroMap1 : H1 G (DiscreteCoind G U A) →+ H1 U A :=
  explicitMap1 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

section Factorization

variable {G U A} (w : G → U) (c : U → A) (hw : Continuous w)
  (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (hccont : Continuous c)
  (hccoc : groupCohomology.IsCocycle₁ c)

omit [CompactSpace G] [DistribMulAction U A] [ContinuousSMul U A] in
include hw hccont in
private theorem continuous_shapiroLift_sub (g : G) :
    Continuous fun x : G => shapiroLift w c (x * g) - shapiroLift w c x :=
  ((continuous_shapiroLift w c hw hccont).comp (continuous_mul_const g)).sub
    (continuous_shapiroLift w c hw hccont)

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TopologicalSpace A]
  [DiscreteTopology A] [ContinuousSMul U A] in
include hwmul hccoc in
private theorem shapiroLift_sub_mul (g : G) (u : U) (x : G) :
    shapiroLift w c ((u : G) * x * g) - shapiroLift w c ((u : G) * x) =
      u • (shapiroLift w c (x * g) - shapiroLift w c x) := by
  rw [mul_assoc, shapiroLift_mul w c hwmul hccoc u (x * g), shapiroLift_mul w c hwmul hccoc u x,
    smul_sub]
  abel

/-- **The inverse Shapiro cochain in degree one.** From a continuous `1`-cocycle `c` of `U` and a
continuous factorization `w` of `G` over the right cosets of `U`, the `1`-cochain of `G` with
coefficients in `Coind_U^G A` whose value at `g` is the right-translation difference
`x ↦ c (w (x * g)) - c (w x)` of `TauCeti.ContCohomology.shapiroLift`. -/
noncomputable def coindCochain1 (g : G) : DiscreteCoind G U A :=
  DiscreteCoind.mk G U A (fun x => shapiroLift w c (x * g) - shapiroLift w c x)
    ((IsLocallyConstant.iff_continuous _).2 (continuous_shapiroLift_sub w c hw hccont g))
    (shapiroLift_sub_mul w c hwmul hccoc g)

omit [CompactSpace G] [ContinuousSMul U A] in
@[simp]
theorem coindCochain1_apply (g x : G) :
    coindCochain1 w c hw hwmul hccont hccoc g x = c (w (x * g)) - c (w x) := (rfl)

omit [ContinuousSMul U A] in
/-- The inverse Shapiro cochain is a continuous `1`-cocycle. It is locally constant because the
lift is *uniformly* locally constant on the compact group `G`
(`TauCeti.isOpen_rightTranslationStabilizer`), and the cocycle identity is the telescoping of its
right-translation differences. -/
theorem coindCochain1_mem_Z1 :
    coindCochain1 w c hw hwmul hccont hccoc ∈ Z1 G (DiscreteCoind G U A) := by
  have hlc : IsLocallyConstant (coindCochain1 w c hw hwmul hccont hccoc) := by
    have hS : IsOpen (rightTranslationStabilizer (shapiroLift w c) : Set G) :=
      isOpen_rightTranslationStabilizer
        ((IsLocallyConstant.iff_continuous _).2 (continuous_shapiroLift w c hw hccont))
    refine (IsLocallyConstant.iff_exists_open _).2 fun g₀ =>
      ⟨(fun g => g₀⁻¹ * g) ⁻¹' (rightTranslationStabilizer (shapiroLift w c) : Set G),
        hS.preimage (continuous_const.mul continuous_id), by simp, fun g hg => ?_⟩
    refine DiscreteCoind.ext fun x => ?_
    have hx := (mem_rightTranslationStabilizer.1 hg) (x * g₀)
    rw [show x * g₀ * (g₀⁻¹ * g) = x * g by group] at hx
    simp only [coindCochain1_apply, ← shapiroLift_apply w c, hx]
  refine mem_Z1_iff.2 ⟨(IsLocallyConstant.iff_continuous _).1 hlc, fun g h => ?_⟩
  refine DiscreteCoind.ext fun x => ?_
  simp only [DiscreteCoind.coe_add, Pi.add_apply, DiscreteCoind.coe_smul, coindCochain1_apply,
    ← mul_assoc]
  abel

/-- **The inverse Shapiro cochain, as a continuous `1`-cocycle.** -/
noncomputable def coindCocycle1 : Z1 G (DiscreteCoind G U A) :=
  ⟨coindCochain1 w c hw hwmul hccont hccoc, coindCochain1_mem_Z1 w c hw hwmul hccont hccoc⟩

omit [ContinuousSMul U A] in
@[simp]
theorem coe_coindCocycle1 :
    (coindCocycle1 w c hw hwmul hccont hccoc : G → DiscreteCoind G U A) =
      coindCochain1 w c hw hwmul hccont hccoc := (rfl)

omit [ContinuousSMul U A] in
/-- **The Shapiro image of the inverse cochain is the cocycle it was built from**, up to the
explicit coboundary of `c (w 1)`. That correction term is what makes a normalisation `w 1 = 1`
unnecessary: it is a coboundary whatever the factorization does at `1`. -/
theorem shapiroCocycles1_coindCocycle1 :
    (shapiroCocycles1 G U A (coindCocycle1 w c hw hwmul hccont hccoc) : U → A) =
      c + d0 U A (c (w 1)) := by
  funext u
  have h : c (w (u : G)) = u • c (w 1) + c u := by
    simpa using shapiroLift_mul w c hwmul hccoc u 1
  rw [shapiroCocycles1_apply, coe_coindCocycle1, coindCochain1_apply, one_mul, Pi.add_apply,
    d0_apply, h]
  abel

omit [CompactSpace G] in
include hw hwmul in
/-- The inverse Shapiro cochain of a `1`-coboundary of `U` is a `1`-coboundary of `G`, with the
primitive `x ↦ w x • α` in `Coind_U^G A`. This is what makes the inverse construction descend to
cohomology. -/
theorem coindCochain1_mem_B1_of_mem_B1 (hcB : c ∈ B1 U A) :
    coindCochain1 w c hw hwmul hccont hccoc ∈ B1 G (DiscreteCoind G U A) := by
  obtain ⟨α, hα⟩ := mem_B1_iff.1 hcB
  refine mem_B1_iff.2 ⟨DiscreteCoind.mk G U A (fun x => w x • α)
    ((IsLocallyConstant.iff_continuous _).2 (continuous_smul.comp (hw.prodMk continuous_const)))
    (fun u x => by rw [hwmul u x, mul_smul]), fun g => DiscreteCoind.ext fun x => ?_⟩
  simp only [DiscreteCoind.coe_sub, Pi.sub_apply, DiscreteCoind.coe_smul,
    DiscreteCoind.mk_apply, coindCochain1_apply, ← hα]
  abel

omit [CompactSpace G] [ContinuousSMul U A] in
/-- **Every continuous `1`-cocycle of `G` is rebuilt from its Shapiro image**, up to the explicit
coboundary whose primitive is `y ↦ (f y) 1 - c (w y)`, where `c` is the Shapiro image of `f`. With
`TauCeti.ContCohomology.shapiroCocycles1_coindCocycle1` this is what makes the Shapiro map
bijective. -/
theorem sub_coindCochain1_mem_B1 (f : Z1 G (DiscreteCoind G U A))
    (hfc : (shapiroCocycles1 G U A f : U → A) = c) :
    (f : G → DiscreteCoind G U A) - coindCochain1 w c hw hwmul hccont hccoc ∈
      B1 G (DiscreteCoind G U A) := by
  have hfcoc := (mem_Z1_iff.1 f.2).2
  have hval : ∀ (u : U) (y : G), (f : G → DiscreteCoind G U A) ((u : G) * y) 1 =
      u • (f : G → DiscreteCoind G U A) y 1 + c u := fun u y => by
    rw [hfcoc (u : G) y]
    simp [← hfc]
  refine mem_B1_iff.2 ⟨DiscreteCoind.mk G U A
    (fun y => (f : G → DiscreteCoind G U A) y 1 - shapiroLift w c y)
    ((IsLocallyConstant.iff_continuous _).2
      (((DiscreteCoind.continuous_apply G U A 1).comp (mem_Z1_iff.1 f.2).1).sub
        (continuous_shapiroLift w c hw hccont)))
    (fun u y => by
      rw [hval u y, shapiroLift_mul w c hwmul hccoc u y, smul_sub]
      abel), fun g => DiscreteCoind.ext fun x => ?_⟩
  have hkey : (f : G → DiscreteCoind G U A) (x * g) 1 =
      (f : G → DiscreteCoind G U A) g x + (f : G → DiscreteCoind G U A) x 1 := by
    rw [hfcoc x g]
    simp
  simp only [DiscreteCoind.coe_sub, Pi.sub_apply, DiscreteCoind.coe_smul,
    DiscreteCoind.mk_apply, coindCochain1_apply, shapiroLift_apply, hkey]
  abel

end Factorization

section Equivalence

variable [TotallyDisconnectedSpace G]

/-- **The forward Shapiro map in degree one is bijective**, which is Shapiro's lemma. Surjectivity
is `TauCeti.ContCohomology.shapiroCocycles1_coindCocycle1` and injectivity combines
`TauCeti.ContCohomology.sub_coindCochain1_mem_B1` with
`TauCeti.ContCohomology.coindCochain1_mem_B1_of_mem_B1`; both run on a continuous right-coset
factorization, which is where closedness of `U` and profiniteness of `G` are used. -/
theorem bijective_explicitShapiroMap1 (hU : IsClosed (U : Set G)) :
    Function.Bijective (explicitShapiroMap1 G U A) := by
  obtain ⟨w, -, hw, -, -, hwmul, -, -⟩ := exists_continuous_rightCosetFactorization U hU
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [explicitMap1_mk] at hx
      have h1 := coindCochain1_mem_B1_of_mem_B1 w ((shapiroCocycles1 G U A f : U → A)) hw hwmul
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).1
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).2 (H1pi_eq_zero_iff.1 hx)
      have h2 := sub_coindCochain1_mem_B1 w ((shapiroCocycles1 G U A f : U → A)) hw hwmul
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).1
        (mem_Z1_iff.1 (shapiroCocycles1 G U A f).2).2 f rfl
      exact H1pi_eq_zero_iff.2 (by simpa using (B1 G (DiscreteCoind G U A)).add_mem h2 h1)
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | _ c =>
      refine ⟨(coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2 :
        H1 G (DiscreteCoind G U A)), ?_⟩
      rw [explicitMap1_mk]
      refine H1pi_eq_iff.2 ?_
      have hsub : (shapiroCocycles1 G U A
          (coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2) :
            U → A) - (c : U → A) = d0 U A ((c : U → A) (w 1)) := by
        rw [shapiroCocycles1_coindCocycle1]
        abel
      rw [hsub]
      exact mem_B1_iff.2 ⟨_, fun g => (d0_apply _ g).symm⟩

/-- **Shapiro's lemma in degree one**, `H¹(G, Coind_U^G A) ≅ H¹(U, A)`, for a profinite `G` and a
closed subgroup `U`. The forward map is restriction to `U` followed by evaluation at `1`, and it
involves no choice; the continuous section of `G → G ⧸ U` is used only to prove it bijective. -/
noncomputable def explicitShapiro1 (hU : IsClosed (U : Set G)) :
    H1 G (DiscreteCoind G U A) ≃+ H1 U A :=
  AddEquiv.ofBijective (explicitShapiroMap1 G U A) (bijective_explicitShapiroMap1 G U A hU)

@[simp]
theorem explicitShapiro1_apply (hU : IsClosed (U : Set G)) (x : H1 G (DiscreteCoind G U A)) :
    explicitShapiro1 G U A hU x = explicitShapiroMap1 G U A x := (rfl)

/-- The inverse of the Shapiro isomorphism is the section formula, for **every** continuous
right-coset factorization of `G` over `U`. Since the equivalence is pinned by its forward
direction, independence of the factorization needs no separate proof. -/
theorem explicitShapiro1_symm_apply (hU : IsClosed (U : Set G)) {w : G → U} (hw : Continuous w)
    (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (c : Z1 U A) :
    (explicitShapiro1 G U A hU).symm (c : H1 U A) =
      (coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2 :
        H1 G (DiscreteCoind G U A)) := by
  refine (AddEquiv.symm_apply_eq _).2 ?_
  rw [explicitShapiro1_apply, explicitMap1_mk]
  refine H1pi_eq_iff.2 ?_
  have hsub : (c : U → A) - (shapiroCocycles1 G U A
      (coindCocycle1 w (c : U → A) hw hwmul (mem_Z1_iff.1 c.2).1 (mem_Z1_iff.1 c.2).2) : U → A) =
      -d0 U A ((c : U → A) (w 1)) := by
    rw [shapiroCocycles1_coindCocycle1]
    abel
  rw [hsub]
  exact (B1 U A).neg_mem (mem_B1_iff.2 ⟨_, fun g => (d0_apply _ g).symm⟩)

end Equivalence

end DegreeOne

section DegreeTwo

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) (A : Type v) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction U A] [ContinuousSMul U A]

/-- **The forward Shapiro map on continuous `2`-cocycles**: restrict a continuous `2`-cocycle of
`G` with coefficients in `Coind_U^G A` to `U`, and evaluate its values at `1`. -/
noncomputable abbrev shapiroCocycles2 : Z2 G (DiscreteCoind G U A) →+ Z2 U A :=
  cocyclesMap2 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

omit [CompactSpace G] [ContinuousSMul U A] in
@[simp]
theorem shapiroCocycles2_apply (f : Z2 G (DiscreteCoind G U A)) (u v : U) :
    (shapiroCocycles2 G U A f : U × U → A) (u, v) =
      (f : G × G → DiscreteCoind G U A) ((u : G), (v : G)) 1 := by
  simp [cocyclesMap2_apply]

/-- **The forward Shapiro map on `H²`**, the compatible-pair pullback along the inclusion `U ↪ G`
and evaluation at `1`. `TauCeti.ContCohomology.explicitShapiro2` upgrades it to an
isomorphism. -/
noncomputable abbrev explicitShapiroMap2 : H2 G (DiscreteCoind G U A) →+ H2 U A :=
  explicitMap2 G (DiscreteCoind G U A) U A (ContinuousMonoidHom.subgroupSubtype U)
    (DiscreteCoind.eval G U A) DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)

variable {G U A}

omit [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] in
/-- The homogeneous form of a `2`-cochain with coinduced coefficients, evaluated at `1`, recovers
the cochain along the three points `y`, `y g`, `y g h`. -/
theorem homogeneous2_apply_one (f : G × G → DiscreteCoind G U A) (y g h : G) :
    (homogeneous2 f y (y * g) (y * g * h) : DiscreteCoind G U A) 1 = f (g, h) y := by
  have hy : y⁻¹ * (y * g) = g := by group
  have hyg : (y * g)⁻¹ * (y * g * h) = h := by group
  rw [homogeneous2_apply, hy, hyg, DiscreteCoind.coe_smul, one_mul]

omit [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] in
/-- At a point of `U` the homogeneous form of a `2`-cochain with coinduced coefficients is
evaluated at `1` by the defining equivariance. This is the shape in which its continuity is
read off. -/
theorem homogeneous2_coe_apply_one (f : G × G → DiscreteCoind G U A) (u : U) (h₁ h₂ : G) :
    (homogeneous2 f (u : G) h₁ h₂ : DiscreteCoind G U A) 1 =
      u • f ((u : G)⁻¹ * h₁, h₁⁻¹ * h₂) 1 := by
  simp [homogeneous2_apply, DiscreteCoind.coe_smul]

omit [CompactSpace G] [ContinuousSMul U A] in
/-- **The Shapiro image has the restricted homogeneous form.** Read at points of `U` and evaluated
at `1`, the homogeneous form of a continuous `2`-cocycle of `G` with coinduced coefficients is the
homogeneous form of its Shapiro image. -/
theorem homogeneous2_shapiroCocycles2 (f : Z2 G (DiscreteCoind G U A)) (u₀ u₁ u₂ : U) :
    homogeneous2 (shapiroCocycles2 G U A f : U × U → A) u₀ u₁ u₂ =
      (homogeneous2 (f : G × G → DiscreteCoind G U A) (u₀ : G) (u₁ : G) (u₂ : G) :
        DiscreteCoind G U A) 1 := by
  rw [homogeneous2_coe_apply_one, homogeneous2_apply, shapiroCocycles2_apply]
  push_cast
  rfl

section Factorization

variable (w : G → U) (c : U × U → A) (hw : Continuous w)
  (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (hccont : Continuous c)

/-- **The inverse Shapiro cochain in degree two.** From a continuous `2`-cocycle `c` of `U` and a
continuous factorization `w` of `G` over the right cosets of `U`, the `2`-cochain of `G` with
coefficients in `Coind_U^G A` whose value at `(g, h)` is the function
`y ↦ homogeneous2 c (w y) (w (y * g)) (w (y * g * h))`: the homogeneous form of `c` read at the
three points `y`, `y g`, `y g h` of `G` pushed into `U` by `w`. -/
noncomputable def coindCochain2 (q : G × G) : DiscreteCoind G U A :=
  DiscreteCoind.mk G U A (fun y => homogeneous2 c (w y) (w (y * q.1)) (w (y * q.1 * q.2)))
    ((IsLocallyConstant.iff_continuous _).2 (continuous_homogeneous2 hccont hw
      (hw.comp (continuous_mul_const _))
      (hw.comp ((continuous_mul_const _).comp (continuous_mul_const _)))))
    (fun u y => by
      have h2 : (u : G) * y * q.1 * q.2 = (u : G) * (y * q.1 * q.2) := by group
      have h1 : (u : G) * y * q.1 = (u : G) * (y * q.1) := by group
      rw [h2, h1, hwmul u y, hwmul u (y * q.1), hwmul u (y * q.1 * q.2)]
      exact homogeneous2_smul c u (w y) (w (y * q.1)) (w (y * q.1 * q.2)))

omit [CompactSpace G] in
@[simp]
theorem coindCochain2_apply (g h y : G) :
    coindCochain2 w c hw hwmul hccont (g, h) y =
      homogeneous2 c (w y) (w (y * g)) (w (y * g * h)) := (rfl)

omit [CompactSpace G] in
/-- The inverse Shapiro cochain satisfies the `2`-cocycle identity: at each `y` it is the
four-term homogeneous relation for `c` at the four points `w y`, `w (y g)`, `w (y g h)`,
`w (y g h j)`. -/
theorem isCocycle₂_coindCochain2 (hccoc : groupCohomology.IsCocycle₂ c) :
    groupCohomology.IsCocycle₂ (coindCochain2 w c hw hwmul hccont) := by
  intro g h j
  refine DiscreteCoind.ext fun y => ?_
  simp only [DiscreteCoind.coe_add, Pi.add_apply, DiscreteCoind.coe_smul, coindCochain2_apply]
  have e1 : y * (g * h) = y * g * h := by group
  have e2 : y * g * (h * j) = y * g * h * j := by group
  rw [e1, e2]
  exact (homogeneous2_add_eq_add hccoc (w y) (w (y * g)) (w (y * g * h))
    (w (y * g * h * j))).symm

/-- The inverse Shapiro cochain is a continuous `2`-cocycle: local constancy in `(g, h)` is
uniform local constancy of the homogeneous form of `c` read through `w`, on the compact group
`G × G × G`. -/
theorem coindCochain2_mem_Z2 (hccoc : groupCohomology.IsCocycle₂ c) :
    coindCochain2 w c hw hwmul hccont ∈ Z2 G (DiscreteCoind G U A) := by
  refine mem_Z2_iff.2 ⟨(IsLocallyConstant.iff_continuous _).1 ?_,
    isCocycle₂_coindCochain2 w c hw hwmul hccont hccoc⟩
  have hQ : IsLocallyConstant fun p : G × G × G =>
      homogeneous2 c (w p.1) (w p.2.1) (w p.2.2) :=
    (IsLocallyConstant.iff_continuous _).2 (continuous_homogeneous2 hccont
      (hw.comp continuous_fst) (hw.comp (continuous_fst.comp continuous_snd))
      (hw.comp (continuous_snd.comp continuous_snd)))
  refine (IsLocallyConstant.iff_exists_open _).2 fun q₀ => ?_
  obtain ⟨V, hVopen, hq₀, hV⟩ := exists_isOpen_translate₃ hQ q₀
  exact ⟨V, hVopen, hq₀, fun q hq => DiscreteCoind.ext fun y => hV q hq y⟩

/-- **The inverse Shapiro cochain, as a continuous `2`-cocycle.** -/
noncomputable def coindCocycle2 (hccoc : groupCohomology.IsCocycle₂ c) :
    Z2 G (DiscreteCoind G U A) :=
  ⟨coindCochain2 w c hw hwmul hccont, coindCochain2_mem_Z2 w c hw hwmul hccont hccoc⟩

@[simp]
theorem coe_coindCocycle2 (hccoc : groupCohomology.IsCocycle₂ c) :
    (coindCocycle2 w c hw hwmul hccont hccoc : G × G → DiscreteCoind G U A) =
      coindCochain2 w c hw hwmul hccont := (rfl)

/-- **The Shapiro image of the inverse cochain is the cocycle it was built from.** Unlike degree
one there is no correction term: a normalized factorization is the identity on `U`, so the three
points read by the inverse cochain at `y = 1` are `1`, `u₁` and `u₁ u₂`. -/
theorem shapiroCocycles2_coindCocycle2 (hccoc : groupCohomology.IsCocycle₂ c) (hw1 : w 1 = 1) :
    (shapiroCocycles2 G U A (coindCocycle2 w c hw hwmul hccont hccoc) : U × U → A) = c := by
  have hwu : ∀ u : U, w (u : G) = u := fun u => by
    have h := hwmul u 1
    rwa [mul_one, hw1, mul_one] at h
  refine funext fun q => ?_
  obtain ⟨u₁, u₂⟩ := q
  have hcoe : ((u₁ : G) * (u₂ : G)) = ((u₁ * u₂ : U) : G) := (Subgroup.coe_mul U u₁ u₂).symm
  rw [shapiroCocycles2_apply, coe_coindCocycle2, coindCochain2_apply, one_mul, hwu u₁, hw1, hcoe,
    hwu (u₁ * u₂), homogeneous2_one_left]
  simp

include hw hwmul hccont in
/-- The inverse Shapiro cochain of a `2`-coboundary of `U` is a `2`-coboundary of `G`, with the
primitive `y ↦ homogeneous1 α (w y) (w (y * g))` built from a primitive `α` of `c`. This is what
makes the inverse construction descend to cohomology. -/
theorem coindCochain2_mem_B2_of_mem_B2 (hcB : c ∈ B2 U A) :
    coindCochain2 w c hw hwmul hccont ∈ B2 G (DiscreteCoind G U A) := by
  obtain ⟨α, hαcont, hα⟩ := mem_B2_iff.1 hcB
  have hN : IsLocallyConstant fun p : G × G => homogeneous1 α (w p.1) (w p.2) :=
    (IsLocallyConstant.iff_continuous _).2 (continuous_homogeneous1 hαcont
      (hw.comp continuous_fst) (hw.comp continuous_snd))
  refine mem_B2_iff.2 ⟨fun g => DiscreteCoind.mk G U A
    (fun y => homogeneous1 α (w y) (w (y * g)))
    ((IsLocallyConstant.iff_continuous _).2 (continuous_homogeneous1 hαcont hw
      (hw.comp (continuous_mul_const _))))
    (fun u y => by
      have h1 : (u : G) * y * g = (u : G) * (y * g) := by group
      rw [h1, hwmul u y, hwmul u (y * g)]
      exact homogeneous1_smul α u (w y) (w (y * g))), ?_, ?_⟩
  · rw [← IsLocallyConstant.iff_continuous]
    refine (IsLocallyConstant.iff_exists_open _).2 fun g₀ => ?_
    obtain ⟨V, hVopen, hg₀, hV⟩ := exists_isOpen_translate₂ hN g₀
    exact ⟨V, hVopen, hg₀, fun g hg => DiscreteCoind.ext fun y => hV g hg y⟩
  · refine funext fun q => ?_
    obtain ⟨g, h⟩ := q
    refine DiscreteCoind.ext fun y => ?_
    simp only [d1_apply, DiscreteCoind.coe_add, DiscreteCoind.coe_sub, Pi.add_apply,
      Pi.sub_apply, DiscreteCoind.coe_smul, DiscreteCoind.mk_apply, coindCochain2_apply, ← hα]
    have hy : y * (g * h) = y * g * h := by group
    rw [hy, homogeneous2_d1]

omit [CompactSpace G] [ContinuousSMul U A] in
/-- The `A`-valued function assembling the primitive that rebuilds a continuous `2`-cocycle of `G`
from its Shapiro image: the comparison function
`TauCeti.ContCohomology.homogeneousHomotopy2` of `f` along `w`, evaluated at `1`. -/
private noncomputable def shapiroPrimitive2 (f : G × G → DiscreteCoind G U A) (p : G × G) : A :=
  (homogeneousHomotopy2 f (fun x : G => ((w x : U) : G)) p.1 p.2 : DiscreteCoind G U A) 1

omit [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] in
/-- The defining formula for the primitive, with the pair argument spelled out. -/
private theorem shapiroPrimitive2_eq (f : G × G → DiscreteCoind G U A) (a b : G) :
    shapiroPrimitive2 w f (a, b) =
      (homogeneousHomotopy2 f (fun x : G => ((w x : U) : G)) a b : DiscreteCoind G U A) 1 := (rfl)

omit [CompactSpace G] in
include hw in
/-- Continuity of the primitive: both of its terms evaluate the cocycle at `1`, by the defining
equivariance of the coinduced module. -/
private theorem continuous_shapiroPrimitive2 (f : G × G → DiscreteCoind G U A)
    (hf : Continuous f) : Continuous (shapiroPrimitive2 w f) := by
  have hwa : Continuous fun p : G × G => w p.1 := hw.comp continuous_fst
  have hwb : Continuous fun p : G × G => w p.2 := hw.comp continuous_snd
  have hva : Continuous fun p : G × G => ((w p.1 : U) : G) := continuous_subtype_val.comp hwa
  have hvb : Continuous fun p : G × G => ((w p.2 : U) : G) := continuous_subtype_val.comp hwb
  have hkey : shapiroPrimitive2 w f = fun p : G × G =>
      w p.1 • f (((w p.1 : U) : G)⁻¹ * p.1, p.1⁻¹ * p.2) 1 -
        w p.1 • f (((w p.1 : U) : G)⁻¹ * ((w p.2 : U) : G), ((w p.2 : U) : G)⁻¹ * p.2) 1 := by
    funext p
    obtain ⟨a, b⟩ := p
    rw [shapiroPrimitive2_eq, homogeneousHomotopy2_apply]
    simp only [DiscreteCoind.coe_sub, Pi.sub_apply]
    rw [homogeneous2_coe_apply_one, homogeneous2_coe_apply_one]
  rw [hkey]
  exact (continuous_smul.comp (hwa.prodMk ((DiscreteCoind.continuous_apply G U A 1).comp
      (hf.comp ((hva.inv.mul continuous_fst).prodMk (continuous_fst.inv.mul continuous_snd)))))).sub
    (continuous_smul.comp (hwa.prodMk ((DiscreteCoind.continuous_apply G U A 1).comp
      (hf.comp ((hva.inv.mul hvb).prodMk (hvb.inv.mul continuous_snd))))))

omit [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul U A] in
include hwmul in
/-- The primitive is `U`-equivariant in its two arguments jointly, which is what makes each of its
sections an element of the coinduced module. -/
private theorem shapiroPrimitive2_smul (f : G × G → DiscreteCoind G U A) (u : U) (a b : G) :
    shapiroPrimitive2 w f ((u : G) * a, (u : G) * b) = u • shapiroPrimitive2 w f (a, b) := by
  have hv : ∀ x : G, ((w ((u : G) * x) : U) : G) = (u : G) * ((w x : U) : G) := by
    intro x
    rw [hwmul u x]
    exact Subgroup.coe_mul U u (w x)
  rw [shapiroPrimitive2_eq, shapiroPrimitive2_eq,
    homogeneousHomotopy2_smul f (fun x : G => ((w x : U) : G)) hv a b,
    DiscreteCoind.coe_smul, one_mul, DiscreteCoind.apply_coe]

include hw hwmul hccont in
/-- **Every continuous `2`-cocycle of `G` is rebuilt from its Shapiro image**, up to the explicit
coboundary whose primitive is the comparison function of
`TauCeti.ContCohomology.homogeneous2_sub_comp` along `w`, evaluated at `1`. With
`TauCeti.ContCohomology.shapiroCocycles2_coindCocycle2` this is what makes the Shapiro map
bijective. -/
theorem sub_coindCochain2_mem_B2 (f : Z2 G (DiscreteCoind G U A))
    (hfc : (shapiroCocycles2 G U A f : U × U → A) = c) :
    (f : G × G → DiscreteCoind G U A) - coindCochain2 w c hw hwmul hccont ∈
      B2 G (DiscreteCoind G U A) := by
  have hfcont : Continuous (f : G × G → DiscreteCoind G U A) := (mem_Z2_iff.1 f.2).1
  have hfcoc : groupCohomology.IsCocycle₂ (f : G × G → DiscreteCoind G U A) :=
    (mem_Z2_iff.1 f.2).2
  have hN : IsLocallyConstant (shapiroPrimitive2 w (f : G × G → DiscreteCoind G U A)) :=
    (IsLocallyConstant.iff_continuous _).2
      (continuous_shapiroPrimitive2 w hw (f : G × G → DiscreteCoind G U A) hfcont)
  refine mem_B2_iff.2 ⟨fun g => DiscreteCoind.mk G U A
    (fun y => shapiroPrimitive2 w (f : G × G → DiscreteCoind G U A) (y, y * g))
    ((IsLocallyConstant.iff_continuous _).2
      (hN.continuous.comp (continuous_id.prodMk (continuous_mul_const g))))
    (fun u y => by
      have hu : (u : G) * y * g = (u : G) * (y * g) := by group
      rw [hu]
      exact shapiroPrimitive2_smul w hwmul (f : G × G → DiscreteCoind G U A) u y (y * g)),
    ?_, ?_⟩
  · rw [← IsLocallyConstant.iff_continuous]
    refine (IsLocallyConstant.iff_exists_open _).2 fun g₀ => ?_
    obtain ⟨V, hVopen, hg₀, hV⟩ := exists_isOpen_translate₂ hN g₀
    exact ⟨V, hVopen, hg₀, fun g hg => DiscreteCoind.ext fun y => hV g hg y⟩
  · refine funext fun q => ?_
    obtain ⟨g, h⟩ := q
    refine DiscreteCoind.ext fun y => ?_
    have key := congrArg (fun F : DiscreteCoind G U A => F (1 : G))
      (homogeneous2_sub_comp hfcoc (fun x : G => ((w x : U) : G)) y (y * g) (y * g * h))
    simp only [DiscreteCoind.coe_sub, DiscreteCoind.coe_add, Pi.sub_apply, Pi.add_apply] at key
    rw [homogeneous2_apply_one] at key
    simp only [d1_apply, DiscreteCoind.coe_sub, DiscreteCoind.coe_add, Pi.sub_apply,
      Pi.add_apply, DiscreteCoind.coe_smul, DiscreteCoind.mk_apply, coindCochain2_apply,
      shapiroPrimitive2_eq]
    have hy : y * (g * h) = y * g * h := by group
    rw [hy, ← hfc, homogeneous2_shapiroCocycles2]
    exact key.symm

end Factorization

section Equivalence

variable (G U A) [TotallyDisconnectedSpace G]

/-- **The forward Shapiro map in degree two is bijective**, which is Shapiro's lemma. Surjectivity
is `TauCeti.ContCohomology.shapiroCocycles2_coindCocycle2` and injectivity combines
`TauCeti.ContCohomology.sub_coindCochain2_mem_B2` with
`TauCeti.ContCohomology.coindCochain2_mem_B2_of_mem_B2`; both run on a continuous right-coset
factorization, which is where closedness of `U` and profiniteness of `G` are used. -/
theorem bijective_explicitShapiroMap2 (hU : IsClosed (U : Set G)) :
    Function.Bijective (explicitShapiroMap2 G U A) := by
  obtain ⟨w, -, hw, -, -, hwmul, -, hw1⟩ := exists_continuous_rightCosetFactorization U hU
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [explicitMap2_mk] at hx
      have hcont : Continuous (shapiroCocycles2 G U A f : U × U → A) :=
        (mem_Z2_iff.1 (shapiroCocycles2 G U A f).2).1
      have h1 := coindCochain2_mem_B2_of_mem_B2 w (shapiroCocycles2 G U A f : U × U → A) hw hwmul
        hcont (H2pi_eq_zero_iff.1 hx)
      have h2 := sub_coindCochain2_mem_B2 w (shapiroCocycles2 G U A f : U × U → A) hw hwmul
        hcont f rfl
      exact H2pi_eq_zero_iff.2 (by simpa using (B2 G (DiscreteCoind G U A)).add_mem h2 h1)
  · intro y
    induction y using QuotientAddGroup.induction_on with
    | _ c =>
      refine ⟨(coindCocycle2 w (c : U × U → A) hw hwmul (mem_Z2_iff.1 c.2).1
        (mem_Z2_iff.1 c.2).2 : H2 G (DiscreteCoind G U A)), ?_⟩
      rw [explicitMap2_mk]
      congr 1
      exact Subtype.ext (shapiroCocycles2_coindCocycle2 w (c : U × U → A) hw hwmul
        (mem_Z2_iff.1 c.2).1 (mem_Z2_iff.1 c.2).2 hw1)

/-- **Shapiro's lemma in degree two**, `H²(G, Coind_U^G A) ≅ H²(U, A)`, for a profinite `G` and a
closed subgroup `U`. The forward map is restriction to `U` followed by evaluation at `1`, and it
involves no choice; the continuous section of `G → G ⧸ U` is used only to prove it bijective. -/
noncomputable def explicitShapiro2 (hU : IsClosed (U : Set G)) :
    H2 G (DiscreteCoind G U A) ≃+ H2 U A :=
  AddEquiv.ofBijective (explicitShapiroMap2 G U A) (bijective_explicitShapiroMap2 G U A hU)

@[simp]
theorem explicitShapiro2_apply (hU : IsClosed (U : Set G)) (x : H2 G (DiscreteCoind G U A)) :
    explicitShapiro2 G U A hU x = explicitShapiroMap2 G U A x := (rfl)

/-- The inverse of the degree-two Shapiro isomorphism is the section formula, for every continuous
right-coset factorization of `G` over `U`. For a normalized factorization the formula is exact on
cocycles; an arbitrary factorization gives the same cohomology class by
`TauCeti.ContCohomology.sub_coindCochain2_mem_B2`. -/
theorem explicitShapiro2_symm_apply (hU : IsClosed (U : Set G)) {w : G → U} (hw : Continuous w)
    (hwmul : ∀ (u : U) (g : G), w ((u : G) * g) = u * w g) (c : Z2 U A) :
    (explicitShapiro2 G U A hU).symm (c : H2 U A) =
      (coindCocycle2 w (c : U × U → A) hw hwmul (mem_Z2_iff.1 c.2).1 (mem_Z2_iff.1 c.2).2 :
        H2 G (DiscreteCoind G U A)) := by
  obtain ⟨w₀, -, hw₀, -, -, hwmul₀, -, hw₀1⟩ :=
    exists_continuous_rightCosetFactorization U hU
  let f₀ : Z2 G (DiscreteCoind G U A) := coindCocycle2 w₀ (c : U × U → A) hw₀ hwmul₀
    (mem_Z2_iff.1 c.2).1 (mem_Z2_iff.1 c.2).2
  have hf₀ : (shapiroCocycles2 G U A f₀ : U × U → A) = c :=
    shapiroCocycles2_coindCocycle2 w₀ (c : U × U → A) hw₀ hwmul₀
      (mem_Z2_iff.1 c.2).1 (mem_Z2_iff.1 c.2).2 hw₀1
  calc
    (explicitShapiro2 G U A hU).symm (c : H2 U A) = (f₀ : H2 G (DiscreteCoind G U A)) := by
      refine (AddEquiv.symm_apply_eq _).2 ?_
      rw [explicitShapiro2_apply, explicitMap2_mk]
      exact congrArg (H2pi U A) (Subtype.ext hf₀.symm)
    _ = (coindCocycle2 w (c : U × U → A) hw hwmul (mem_Z2_iff.1 c.2).1
        (mem_Z2_iff.1 c.2).2 : H2 G (DiscreteCoind G U A)) := by
      refine H2pi_eq_iff.2 ?_
      exact sub_coindCochain2_mem_B2 w (c : U × U → A) hw hwmul
        (mem_Z2_iff.1 c.2).1 f₀ hf₀

end Equivalence

end DegreeTwo


end TauCeti.ContCohomology
