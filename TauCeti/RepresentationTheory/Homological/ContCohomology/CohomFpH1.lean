/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Topology.Homology
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1ZMod
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Homogeneous
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp

/-!
# `H¹` with `ZMod n` coefficients is the continuous cohomology of `cohomFp`

`TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` identifies the inhomogeneous
`H¹(G, M)` of a discrete `G`-module `M` with the continuous cohomology of the object
`TauCeti.ContCohomology.ofDiscreteModule ℤ G M`, whose coefficient ring is `ℤ`. The coefficients
the roadmap asks about, `TauCeti.cohomFp n G 1`, live in a different object,
`TauCeti.trivialFp n G`, whose coefficient ring is `ZMod n` and whose carrier is the universe
lift of `ZMod n`; this file identifies the two.

The merged comparison cannot be transported to the second object: it is stated for the `ℤ`
coefficient ring, and `TauCeti.trivialFp n G` is not of the form
`TauCeti.ContCohomology.ofDiscreteModule R G M` for any `R`, being the `ZMod n`-module with the
trivial action rather than the module for a given action over `ℤ`. What is shared between the two
objects is the shape of their cochain spaces, so the degree-one comparison is rebuilt here for
`TauCeti.trivialFp n G` out of the same inhomogeneous building blocks
(`TauCeti.ContCohomology.homogeneous1`, `TauCeti.ContCohomology.Z1`,
`TauCeti.ContCohomology.B1`) that the `ℤ` comparison uses, and not by any new construction of
continuous cohomology.

The comparison is the inhomogeneous cocycle description of `H¹(G, 𝔽_n)` in degree one: with
trivial coefficients a continuous `1`-cocycle is a continuous homomorphism `G → (𝔽_n, +)`, its
`1`-coboundaries vanish, and the corresponding canonical `1`-cocycle is its homogeneous form
`(g, h) ↦ c (g⁻¹ * h)`. Nothing here needs `n` to be prime, profiniteness, or a pro-`p`
hypothesis; those belong to the theorems which compute the rank of the result, in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.H1Dual`.

The carrier of `TauCeti.trivialFp n G` is *defined* to be the universe lift of `ZMod n` and its
action to be trivial, and `TauCeti.trivialFp`'s body is `@[expose]`d, so the explicit
`ULift`-valued statements below and the canonical cochain spaces are the same spaces
definitionally. That is what makes this file a change of coordinates on the cochains of
`TauCeti.trivialFp n G` rather than a second construction of continuous cohomology with these
coefficients.

## Main definitions

* `TauCeti.ContCohomology.cohomFpCocycleEquiv1`: continuous inhomogeneous `1`-cocycles of the
  lifted `ZMod n` coefficients are the canonical `1`-cocycles of `TauCeti.trivialFp n G`.
* `TauCeti.ContCohomology.h1EquivCohomFpULift`: `H¹` of those coefficients is the degree-one
  continuous cohomology of `TauCeti.cohomFp`, as an additive equivalence.
* `TauCeti.h1CoeffEquiv`: transport of `H¹` between the `ZMod n` coefficients and that lifted
  carrier.
* `TauCeti.h1EquivCohomFp`: `H¹(G, 𝔽_n)` is the degree-one continuous cohomology of
  `TauCeti.cohomFp`, as an isomorphism of `ZMod n`-modules.

## Main results

* `TauCeti.ContCohomology.cohomFpCocycleEquiv1_symm_apply`,
  `TauCeti.ContCohomology.h1EquivCohomFpULift_apply_mk` and
  `TauCeti.ContCohomology.h1EquivCohomFpULift_symm_apply`: the comparison in both directions, over
  the lifted carrier.
* `TauCeti.h1EquivCohomFp_apply_mk` and `TauCeti.h1EquivCohomFp_symm_apply`: the comparison in
  both directions, the class of a continuous `1`-cocycle being sent to the canonical cohomology
  class of the cocycle it defines, and a canonical cohomology class being sent back to the class
  of the continuous `1`-cocycle it carries.
* `TauCeti.h1CoeffEquiv_apply_mk` and `TauCeti.h1CoeffEquiv_symm_apply`: the same formulas for the
  coefficient transport, so that both directions of that transport are computed by `simp` without
  unfolding. `TauCeti.ContCohomology.cohomFpCocycleEquiv1_apply` is the forward value formula of
  the cocycle comparison; it is applied by name rather than by `simp`, because its left-hand side
  mentions the carrier of a canonical `1`-cocycle and so is not in simp normal form (see its
  docstring).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §2, where
  the inhomogeneous and homogeneous descriptions of the standard complex are compared.
* `TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison`, whose `ℤ`
  version of this comparison is the `ℤ`-coefficient counterpart of this file.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology

universe u

section Canonical

variable (n : ℕ) (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The action on the lifted carrier of `TauCeti.trivialFp n G` is the trivial one, as the
coefficient object of a trivial action. The canonical cochains read it from
`TauCeti.trivialFp`; the explicit inhomogeneous cochains of `LowDegree.lean` need it as an
ambient `DistribMulAction`. -/
instance instDistribMulActionULiftZMod : DistribMulAction G (ULift.{u} (ZMod n)) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_add _ _ _ := rfl
  smul_zero _ := rfl

/-- The trivial action on the lifted carrier is continuous, being independent of its first
variable. -/
instance instContinuousSMulULiftZMod : ContinuousSMul G (ULift.{u} (ZMod n)) where
  continuous_smul := ⟨fun _s hs => hs.preimage continuous_snd⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The action of the lifted carrier is trivial, as a rewrite rule. -/
@[simp]
private theorem smul_trivial (g : G) (m : ULift.{u} (ZMod n)) : g • m = m := (rfl)

/-- A homogeneous zero-cochain of the coefficient object is determined by its value at the
identity: it is a constant, and the action is trivial. -/
private theorem smul_canonical0 (c : (trivialFp n G).ρ.coind₁.invariants) (g : G) :
    (SMul.smul g : ULift.{u} (ZMod n) → ULift.{u} (ZMod n)) (c.val 1) = c.val g := by
  have h := congrArg (fun f : C(G, ULift.{u} (ZMod n)) ↦ f g) (c.property g)
  -- The carrier of the coinduced coefficient object is only semireducibly the carrier of
  -- `TauCeti.trivialFp n G`; normalize the coinduction evaluation before simplifying.
  change (SMul.smul g : ULift.{u} (ZMod n) → ULift.{u} (ZMod n)) (c.val (g⁻¹ * g)) = c.val g at h
  simpa using h

/-- A homogeneous one-cochain of the coefficient object is determined by evaluation with first
argument `1`. -/
private theorem smul_canonical1 (c : (trivialFp n G).ρ.coind₁.coind₁.invariants) (g h : G) :
    (SMul.smul g : ULift.{u} (ZMod n) → ULift.{u} (ZMod n)) (c.val 1 (g⁻¹ * h)) = c.val g h := by
  have e := congrArg (fun f : C(G, C(G, ULift.{u} (ZMod n))) ↦ f g h) (c.property g)
  -- As above, normalize the coinduction evaluation before simplifying.
  change (SMul.smul g : ULift.{u} (ZMod n) → ULift.{u} (ZMod n))
    (c.val (g⁻¹ * g) (g⁻¹ * h)) = c.val g h at e
  simpa using e

/-- The constant cochain of the lifted carrier, as a canonical homogeneous zero-cochain. -/
private noncomputable def cochainEquiv0 : (ULift.{u} (ZMod n)) ≃+
    (trivialFp n G).ρ.coind₁.invariants where
  toFun m := ⟨(⟨fun _ ↦ m, continuous_const⟩ : C(G, ULift.{u} (ZMod n))), by
    intro g
    ext h
    -- As above, normalize the coinduction evaluation before simplifying.
    change (SMul.smul g : ULift.{u} (ZMod n) → ULift.{u} (ZMod n)) m = m
    rfl⟩
  invFun c := c.val 1
  left_inv m := rfl
  right_inv c := by
    apply Subtype.ext
    ext g
    exact smul_canonical0 n G c g
  map_add' m m' := by
    apply Subtype.ext
    ext g
    exact smul_add g m m'

/-- `cochainEquiv0` sends `m` to the constant zero-cochain of the coefficient object. -/
@[simp]
private theorem cochainEquiv0_apply (m : ULift.{u} (ZMod n)) (g : G) :
    (cochainEquiv0 n G m).val g = m := (rfl)

/-- Continuous one-cochains of the lifted carrier, as canonical homogeneous one-cochains, by
currying their homogeneous form. -/
private noncomputable def cochainEquiv1 : C1 G (ULift.{u} (ZMod n)) ≃+
    (trivialFp n G).ρ.coind₁.coind₁.invariants where
  toFun c := ⟨ContinuousMap.curry
    (⟨fun p ↦ homogeneous1 c.val p.1 p.2,
      continuous_homogeneous1 (mem_C1_iff.mp c.property) continuous_fst
        continuous_snd⟩ : C(G × G, ULift.{u} (ZMod n))), by
    intro g
    ext h k
    -- As above, normalize the coinduction evaluation before simplifying. The homogeneous form
    -- is equivariant, and the action is trivial, so the canonical invariance condition is
    -- equivariance of `homogeneous1`.
    change (SMul.smul g : ULift.{u} (ZMod n) → ULift.{u} (ZMod n))
      (homogeneous1 (M := ULift.{u} (ZMod n)) c.val (g⁻¹ * h) (g⁻¹ * k)) = homogeneous1 c.val h k
    exact homogeneous1_smul c.val g⁻¹ h k⟩

  invFun c := ⟨c.val 1, mem_C1_iff.mpr (c.val 1).continuous⟩
  left_inv c := by
    apply Subtype.ext
    funext g
    exact homogeneous1_one_left c.val g
  right_inv c := by
    apply Subtype.ext
    ext g h
    exact (homogeneous1_apply (M := ULift.{u} (ZMod n)) (c.val 1) g h).trans
      (smul_canonical1 n G c g h)
  map_add' c d := by
    apply Subtype.ext
    ext g h
    simp only [homogeneous1_apply]
    exact smul_add g (c.val (g⁻¹ * h)) (d.val (g⁻¹ * h))

/-- `cochainEquiv1` sends a continuous `1`-cochain to its homogeneous form, curried. -/
@[simp]
private theorem cochainEquiv1_apply (c : C1 G (ULift.{u} (ZMod n))) (g h : G) :
    (cochainEquiv1 n G c).val g h = homogeneous1 c.val g h := (rfl)

/-- The degree-zero comparison carries `d0` to the homogeneous differential of the coefficient
object. Both sides are zero, as the action is trivial, but the statement is the compatibility the
`1`-cocycle comparison needs. -/
private theorem d_cochainEquiv0 (m : ULift.{u} (ZMod n)) :
    ((TopRep.homogeneousCochains (trivialFp n G)).d 0 1).hom (cochainEquiv0 n G m) =
      cochainEquiv1 n G ⟨d0 G (ULift.{u} (ZMod n)) m,
        mem_C1_iff.mpr (continuous_d0_apply m)⟩ := by
  apply Subtype.ext
  rw [TopRep.homogeneousCochains.d_apply]
  ext g h
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom, ContIntertwiningMap.sub_apply,
    ContRepresentation.coind₁ι_toFun, ContRepresentation.coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, cochainEquiv0_apply, cochainEquiv1_apply]
  -- The action of the coefficient object is trivial, so both sides are the zero cochain.
  change m - m = homogeneous1 (M := ULift.{u} (ZMod n)) (d0 G (ULift.{u} (ZMod n)) m) g h
  simp only [homogeneous1_apply, d0_apply, smul_trivial, sub_self]

/-- The differential of the degree-one comparison is the homogeneous form of `d1`. -/
private theorem d_cochainEquiv1_apply (c : C1 G (ULift.{u} (ZMod n))) (g h k : G) :
    (((TopRep.homogeneousCochains (trivialFp n G)).d 1 2).hom
        (cochainEquiv1 n G c)).val g h k =
      g • d1 G (ULift.{u} (ZMod n)) c.val (g⁻¹ * h, h⁻¹ * k) := by
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [TopRep.hom_d_succ, TopRep.d_zero, TopRep.hom_ofHom,
    ContIntertwiningMap.sub_apply, ContRepresentation.coind₁ι_toFun,
    ContRepresentation.coind₁Map_toFun, ContinuousMap.sub_apply,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    cochainEquiv1_apply]
  rw [← homogeneous2_apply, homogeneous2_d1]
  exact (sub_sub_eq_add_sub _ _ _).trans (add_sub_right_comm _ _ _)

/-- The degree-one comparison detects precisely the continuous inhomogeneous `1`-cocycles. -/
private theorem d_cochainEquiv1_eq_zero_iff (c : C1 G (ULift.{u} (ZMod n))) :
    ((TopRep.homogeneousCochains (trivialFp n G)).d 1 2).hom (cochainEquiv1 n G c) = 0 ↔
      c.val ∈ Z1 G (ULift.{u} (ZMod n)) := by
  rw [mem_Z1_iff, and_iff_right (mem_C1_iff.mp c.property), ← d1_apply_eq_zero_iff]
  constructor
  · intro hc
    funext ⟨g, h⟩
    have e := congrArg (fun z => z.val 1 g (g * h)) hc
    rw [d_cochainEquiv1_apply] at e
    -- Normalize the bundled coefficient carrier before simplifying the group coordinates.
    change (1 : G) • d1 G (ULift.{u} (ZMod n)) c.val (1⁻¹ * g, g⁻¹ * (g * h)) =
      (0 : ULift.{u} (ZMod n)) at e
    simpa only [inv_one, one_mul, inv_mul_cancel_left, one_smul, Pi.zero_apply] using e
  · intro hc
    apply Subtype.ext
    ext g h k
    rw [d_cochainEquiv1_apply]
    -- The right side is the zero continuous map, evaluated in the bundled carrier.
    change g • d1 G (ULift.{u} (ZMod n)) c.val (g⁻¹ * h, h⁻¹ * k) = (0 : ULift.{u} (ZMod n))
    rw [hc, Pi.zero_apply, smul_zero]

/-- **Continuous inhomogeneous `1`-cocycles of the lifted `ZMod n` coefficients are the canonical
`1`-cocycles of `TauCeti.trivialFp n G`, as an additive equivalence.** The forward formula is the
homogeneous form `g • c (g⁻¹ * h)` of the cocycle, curried; the inverse evaluates the canonical
cocycle at `(1, g)`. This is the degree-one `ZMod n`-linear part of the comparison: the
coefficients of `TauCeti.cohomFp` lie in `ZMod n`, so the `ℤ`-valued comparison of
`TauCeti.ContCohomology.CocycleComparison` does not apply to them. -/
noncomputable def cohomFpCocycleEquiv1 :
    Z1 G (ULift.{u} (ZMod n)) ≃+ _root_.ContinuousCohomology.cocycles (trivialFp n G) 1 :=
  -- Ascribed: typed on its own, the cochain meets the kernel's carrier in one cheap check.
  ({ toFun c := ⟨(cochainEquiv1 n G ⟨c.val, Z1_le_C1 G (ULift.{u} (ZMod n)) c.property⟩ :),
        (d_cochainEquiv1_eq_zero_iff n G _).mpr c.property⟩
     invFun c := ⟨((cochainEquiv1 n G).symm c.val).val,
        (d_cochainEquiv1_eq_zero_iff n G _).mp (by
          rw [AddEquiv.apply_symm_apply]
          exact c.property)⟩
     left_inv c := by
       apply Subtype.ext
       exact congrArg (fun b : C1 G (ULift.{u} (ZMod n)) => b.val)
         ((cochainEquiv1 n G).symm_apply_apply ⟨c.val,
           Z1_le_C1 G (ULift.{u} (ZMod n)) c.property⟩)
     right_inv c := by
       apply Subtype.ext
       exact (cochainEquiv1 n G).apply_symm_apply c.val
     map_add' c d := by
       apply Subtype.ext
       exact (cochainEquiv1 n G).map_add
         ⟨c.val, Z1_le_C1 G (ULift.{u} (ZMod n)) c.property⟩
         ⟨d.val, Z1_le_C1 G (ULift.{u} (ZMod n)) d.property⟩ } :
      Z1 G (ULift.{u} (ZMod n)) ≃+ TopModuleCat.ker
        ((TopRep.homogeneousCochains (trivialFp n G)).d 1 2)).trans
    -- Ascribed: elaborated alone, the `_` is read off `cyclesIsKernel`, not unified via the kernel.
    ((Limits.IsLimit.conePointUniqueUpToIso (TopModuleCat.isLimitKer _)
      ((TopRep.homogeneousCochains (trivialFp n G)).cyclesIsKernel 1 2
        (by simp))).toContinuousLinearEquiv.toAddEquiv :)

/-- The inverse one-cocycle comparison reads the canonical cocycle at `(1, g)`. -/
@[simp]
theorem cohomFpCocycleEquiv1_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (trivialFp n G) 1) (g : G) :
    ((cohomFpCocycleEquiv1 n G).symm c).val g =
      ((TopRep.homogeneousCochains (trivialFp n G)).iCycles 1 c).val 1 g := by
  obtain ⟨c, rfl⟩ := (cohomFpCocycleEquiv1 n G).surjective c
  -- Read the short-complex inclusion as the inclusion of the homogeneous complex.
  have e : (TopRep.homogeneousCochains (trivialFp n G)).iCycles 1 (cohomFpCocycleEquiv1 n G c) =
      cochainEquiv1 n G ⟨c.val, Z1_le_C1 G (ULift.{u} (ZMod n)) c.property⟩ :=
    ConcreteCategory.congr_hom
      (Limits.IsLimit.conePointUniqueUpToIso_hom_comp (TopModuleCat.isLimitKer _)
        ((TopRep.homogeneousCochains (trivialFp n G)).cyclesIsKernel 1 2 (by simp))
        Limits.WalkingParallelPair.zero) _
  rw [AddEquiv.symm_apply_apply, e, cochainEquiv1_apply]
  simp

/-- The forward one-cocycle comparison is the homogeneous form of the cocycle, curried: at `g` and
`h` it is the value of `c` at `g⁻¹ * h`, the action on the lifted carrier being trivial.

Deliberately not `@[simp]`: the left-hand side is not in simp normal form. Applying a canonical
`1`-cocycle of `TauCeti.trivialFp n G` to a point mentions the carrier
`↑ ((TauCeti.trivialFp n G).resolutionX 1)`, which `simp` rewrites — through
`CategoryTheory.Functor.mapHomologicalComplex_obj_X`, which is how `TopRep.homogeneousCochains`
unfolds — to `C(G, ↑ ((TauCeti.trivialFp n G).resolutionX 0))`, so the linter `simpNF` rejects the
attribute. The value is still computed without unfolding the comparison, by applying this theorem
by name; the inverse direction, whose left-hand side is an inhomogeneous cocycle and so mentions no
canonical cochain carrier, is `TauCeti.ContCohomology.cohomFpCocycleEquiv1_symm_apply`. -/
theorem cohomFpCocycleEquiv1_apply (c : Z1 G (ULift.{u} (ZMod n))) (g h : G) :
    ((TopRep.homogeneousCochains (trivialFp n G)).iCycles 1
      (cohomFpCocycleEquiv1 n G c)).val g h = c.val (g⁻¹ * h) := by
  -- Read the short-complex inclusion as the inclusion of the homogeneous complex.
  have e : (TopRep.homogeneousCochains (trivialFp n G)).iCycles 1 (cohomFpCocycleEquiv1 n G c) =
      cochainEquiv1 n G ⟨c.val, Z1_le_C1 G (ULift.{u} (ZMod n)) c.property⟩ :=
    ConcreteCategory.congr_hom
      (Limits.IsLimit.conePointUniqueUpToIso_hom_comp (TopModuleCat.isLimitKer _)
        ((TopRep.homogeneousCochains (trivialFp n G)).cyclesIsKernel 1 2 (by simp))
        Limits.WalkingParallelPair.zero) _
  rw [e, cochainEquiv1_apply]
  simp
  rfl

/-- The comparison sends the explicit coboundary of an element of the carrier to its canonical
boundary, with the same primitive under the degree-zero cochain comparison. -/
private theorem cohomFpCocycleEquiv1_d0 (m : ULift.{u} (ZMod n)) :
    cohomFpCocycleEquiv1 n G ⟨d0 G (ULift.{u} (ZMod n)) m,
      B1_le_Z1 G (ULift.{u} (ZMod n)) (d0_mem_B1 m)⟩ =
      (TopRep.homogeneousCochains (trivialFp n G)).toCycles 0 1
        (cochainEquiv0 n G m :) := by
  apply (cohomFpCocycleEquiv1 n G).symm.injective
  apply Subtype.ext
  funext g
  rw [AddEquiv.symm_apply_apply, cohomFpCocycleEquiv1_symm_apply]
  have e := ConcreteCategory.congr_hom
    ((TopRep.homogeneousCochains (trivialFp n G)).toCycles_i 0 1)
    (cochainEquiv0 n G m)
  simp only [ConcreteCategory.comp_apply] at e
  rw [e, d_cochainEquiv0]
  simp

/-- A continuous inhomogeneous `1`-cocycle is an explicit coboundary exactly when its canonical
image is a boundary. -/
private theorem mem_B1_iff_cohomFpCocycleEquiv1_mem_range (c : Z1 G (ULift.{u} (ZMod n))) :
    c.val ∈ B1 G (ULift.{u} (ZMod n)) ↔ cohomFpCocycleEquiv1 n G c ∈ Set.range
      ((TopRep.homogeneousCochains (trivialFp n G)).toCycles 0 1) := by
  constructor
  · intro hc
    obtain ⟨m, hm⟩ := mem_B1_iff.mp hc
    refine ⟨cochainEquiv0 n G m, ?_⟩
    rw [← cohomFpCocycleEquiv1_d0]
    exact congrArg (cohomFpCocycleEquiv1 n G) (Subtype.ext (funext fun g =>
      (d0_apply m g).trans (hm g)))
  · rintro ⟨b, hb⟩
    obtain ⟨b, rfl⟩ := (cochainEquiv0 n G).surjective b
    rw [← cohomFpCocycleEquiv1_d0] at hb
    have hd := congrArg Subtype.val ((cohomFpCocycleEquiv1 n G).injective hb)
    exact mem_B1_iff.mpr ⟨b, fun g => (d0_apply b g).symm.trans (congrFun hd g)⟩

/-- The canonical cohomology class of a continuous inhomogeneous `1`-cocycle. -/
private noncomputable def cohomologyClass1 :
    Z1 G (ULift.{u} (ZMod n)) →+ cohomFp n G 1 :=
  ((TopRep.homogeneousCochains (trivialFp n G)).homologyπ 1).hom.toLinearMap.toAddMonoidHom.comp
    (cohomFpCocycleEquiv1 n G).toAddMonoidHom

private theorem cohomologyClass1_eq_zero_iff (c : Z1 G (ULift.{u} (ZMod n))) :
    cohomologyClass1 n G c = 0 ↔ (c : G → ULift.{u} (ZMod n)) ∈ B1 G (ULift.{u} (ZMod n)) := by
  rw [mem_B1_iff_cohomFpCocycleEquiv1_mem_range]
  exact HomologicalComplex.homologyπ_eq_zero_iff _ 1 (by simp)

private theorem cohomologyClass1_surjective : Function.Surjective (cohomologyClass1 n G) := by
  intro y
  obtain ⟨x, hx⟩ := HomologicalComplex.homologyπ_surjective _ 1 y
  refine ⟨(cohomFpCocycleEquiv1 n G).symm x, ?_⟩
  simpa [cohomologyClass1] using hx

private theorem cohomologyClass1_ker :
    (B1 G (ULift.{u} (ZMod n))).addSubgroupOf (Z1 G (ULift.{u} (ZMod n))) =
      (cohomologyClass1 n G).ker := by
  ext c
  rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, cohomologyClass1_eq_zero_iff]

/-- **`H¹` of the universe-lifted `ZMod n` coefficients is the degree-one continuous cohomology
of `TauCeti.cohomFp`, as an additive equivalence.** No hypothesis on `G` beyond being a
topological group is used, and no hypothesis on the action is needed, because the coefficient
object of `TauCeti.cohomFp` carries the trivial action by construction. -/
noncomputable def h1EquivCohomFpULift : H1 G (ULift.{u} (ZMod n)) ≃+ cohomFp n G 1 :=
  QuotientAddGroup.liftEquiv _ (cohomologyClass1_surjective n G) (cohomologyClass1_ker n G)

/-- The comparison sends the class of a continuous `1`-cocycle to the canonical cohomology class
of the homogeneous cocycle it corresponds to. -/
@[simp]
theorem h1EquivCohomFpULift_apply_mk (c : Z1 G (ULift.{u} (ZMod n))) :
    h1EquivCohomFpULift n G (c : H1 G (ULift.{u} (ZMod n))) =
      (TopRep.homogeneousCochains (trivialFp n G)).homologyπ 1 (cohomFpCocycleEquiv1 n G c) :=
  QuotientAddGroup.liftEquiv_coe _ _ _ c

/-- The inverse comparison sends a canonical cohomology class to the class of the inhomogeneous
cocycle it corresponds to. -/
@[simp]
theorem h1EquivCohomFpULift_symm_apply
    (c : _root_.ContinuousCohomology.cocycles (trivialFp n G) 1) :
    (h1EquivCohomFpULift n G).symm ((TopRep.homogeneousCochains (trivialFp n G)).homologyπ 1 c) =
      ((cohomFpCocycleEquiv1 n G).symm c : H1 G (ULift.{u} (ZMod n))) := by
  apply (h1EquivCohomFpULift n G).injective
  rw [AddEquiv.apply_symm_apply, h1EquivCohomFpULift_apply_mk, AddEquiv.apply_symm_apply]

end Canonical

end TauCeti.ContCohomology

/-! ### The comparison over the `ZMod n` coefficients themselves -/

namespace TauCeti

open ContCohomology

universe u

section Coefficients

variable {n : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod n)] [ContinuousSMul G (ZMod n)]

/-- **Transport of `H¹(G, 𝔽_n)` to the universe-lifted carrier of `TauCeti.trivialFp n G`.** The
coefficient object of `TauCeti.cohomFp` is built on the universe lift of `ZMod n`, so the
comparison with its degree-one cohomology is stated there and transported back along
`TauCeti.trivialFpEquiv`. The action on the source is the ambient one, and `htriv` says it is
trivial, so this is the trivial action of the target. -/
noncomputable def h1CoeffEquiv (htriv : ∀ (g : G) (m : ZMod n), g • m = m) :
    H1 G (ZMod n) ≃+ H1 G (ULift.{u} (ZMod n)) :=
  ContCohomology.explicitCoeff1Equiv (G := G) (M := ZMod n) (N := ULift.{u} (ZMod n))
    (trivialFpEquiv n G).symm.toAddEquiv continuous_of_discreteTopology
    continuous_of_discreteTopology (fun g m => by rw [htriv g m]; rfl)

omit [IsTopologicalGroup G] in
/-- **The coefficient transport is postcomposition with the cocycle.** A class of `H¹(G, 𝔽_n)` is
sent to the continuous `1`-cocycle it defines, with its values lifted into the carrier of
`TauCeti.trivialFp n G` by `TauCeti.trivialFpEquiv`. The instance
`TauCeti.ContCohomology.explicitCoeff1_mk` completes the right-hand side to the class of that
cocycle, so with this formula `TauCeti.h1EquivCohomFp_apply_mk` computes a class of
`TauCeti.cohomFp n G 1` from the cocycle itself, with no unfolding. -/
@[simp]
theorem h1CoeffEquiv_apply_mk (htriv : ∀ (g : G) (m : ZMod n), g • m = m)
    (c : Z1 G (ZMod n)) :
    h1CoeffEquiv htriv (c : H1 G (ZMod n)) =
      ContCohomology.explicitCoeff1 G (ZMod n)
        ({ (trivialFpEquiv n G).symm.toAddEquiv.toAddMonoidHom with
            map_smul' := fun g m => by rw [htriv g m]; rfl } :
          ZMod n →+[G] ULift.{u} (ZMod n))
        continuous_of_discreteTopology (c : H1 G (ZMod n)) := by
  unfold h1CoeffEquiv
  exact ContCohomology.explicitCoeff1Equiv_apply (G := G) (M := ZMod n)
    (N := ULift.{u} (ZMod n)) (trivialFpEquiv n G).symm.toAddEquiv
    continuous_of_discreteTopology continuous_of_discreteTopology
    (fun g m => by rw [htriv g m]; rfl) (c : H1 G (ZMod n))

/-- **The inverse coefficient transport reads the values back into `ZMod n`.** A class of the
lifted `H¹` is sent to the class of the `1`-cocycle obtained by postcomposition with
`ULift.moduleEquiv`, the equivalence identifying the lifted carrier with the carrier of
`TauCeti.trivialFp n G`. The argument is the class of a canonical `1`-cocycle, the form
`TauCeti.h1EquivCohomFp_symm_apply` produces. -/
@[simp]
theorem h1CoeffEquiv_symm_apply
    (htriv : ∀ (g : G) (m : ZMod n), g • m = m)
    (c : _root_.ContinuousCohomology.cocycles (trivialFp n G) 1) :
    (h1CoeffEquiv htriv).symm ((cohomFpCocycleEquiv1 n G).symm c :
        H1 G (ULift.{u} (ZMod n))) =
      ContCohomology.explicitCoeff1 G (ULift.{u} (ZMod n))
        ({ (ULift.moduleEquiv : ULift.{u} (ZMod n) ≃ₗ[ZMod n] ZMod n).toAddMonoidHom with
            map_smul' := fun g m => by rw [smul_trivial, htriv] })
        continuous_of_discreteTopology ((cohomFpCocycleEquiv1 n G).symm c :
          H1 G (ULift.{u} (ZMod n))) := by
  rw [h1CoeffEquiv,
    ContCohomology.explicitCoeff1Equiv_symm_apply (G := G) (M := ZMod n)
      (N := ULift.{u} (ZMod n)) (trivialFpEquiv n G).symm.toAddEquiv
      continuous_of_discreteTopology continuous_of_discreteTopology
      (fun g m => by rw [htriv g m]; rfl)
      ((cohomFpCocycleEquiv1 n G).symm c : H1 G (ULift.{u} (ZMod n)))]
  refine congrArg (fun f : ULift.{u} (ZMod n) →+[G] ZMod n =>
    ContCohomology.explicitCoeff1 G (ULift.{u} (ZMod n)) f continuous_of_discreteTopology
      ((cohomFpCocycleEquiv1 n G).symm c : H1 G (ULift.{u} (ZMod n)))) ?_
  ext m
  change (trivialFpEquiv n G) m = ULift.down m
  exact trivialFpEquiv_apply (G := G) (p := n) (x := (m : ULift.{u} (ZMod n)))

/-- **`H¹(G, 𝔽_n)` is the degree-one continuous cohomology of `TauCeti.cohomFp n G`, as an
isomorphism of `ZMod n`-modules.**

A class of `H¹(G, 𝔽_n)` is sent to the canonical cohomology class of the homogeneous cocycle it
defines, read through `TauCeti.trivialFpEquiv` in the universe lift of `ZMod n`. This is the
`ZMod n`-linear degree-one comparison the coefficients of `TauCeti.cohomFp` need, and it is what
makes the rank, finite-dimensionality and cardinality of `TauCeti.cohomFp n G 1` the invariants of
`H¹(G, 𝔽_n)`; the four results computed from it are in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.H1Dual`. The `ZMod n`-module structure on the
source is `TauCeti.instModuleH1`, the one on the target is the canonical one of
`TauCeti.cohomFp`. -/
noncomputable def h1EquivCohomFp (htriv : ∀ (g : G) (m : ZMod n), g • m = m) :
    H1 G (ZMod n) ≃ₗ[ZMod n] cohomFp n G 1 :=
  let e : H1 G (ZMod n) ≃+ cohomFp n G 1 :=
    ((ContCohomology.h1EquivCohomFpULift n G).symm.trans (h1CoeffEquiv htriv).symm).symm
  e.toLinearEquiv (ZMod.map_smul e)

/-- The comparison sends the class of a continuous `1`-cocycle to the canonical cohomology class
of the cocycle it defines. -/
@[simp]
theorem h1EquivCohomFp_apply_mk (htriv : ∀ (g : G) (m : ZMod n), g • m = m)
    (c : Z1 G (ZMod n)) :
    h1EquivCohomFp htriv (c : H1 G (ZMod n)) =
      ContCohomology.h1EquivCohomFpULift n G (h1CoeffEquiv htriv (c : H1 G (ZMod n))) := by
  unfold h1EquivCohomFp
  rfl

/-- The inverse comparison sends a canonical cohomology class to the class of the continuous
`1`-cocycle it corresponds to, read back into `ZMod n`. With
`TauCeti.h1CoeffEquiv_symm_apply` this computes the class of that cocycle, so the comparison can
be used in both directions without unfolding. -/
@[simp]
theorem h1EquivCohomFp_symm_apply (htriv : ∀ (g : G) (m : ZMod n), g • m = m)
    (c : _root_.ContinuousCohomology.cocycles (trivialFp n G) 1) :
    (h1EquivCohomFp htriv).symm
        ((TopRep.homogeneousCochains (trivialFp n G)).homologyπ 1 c) =
      (((h1CoeffEquiv htriv).symm
          ((cohomFpCocycleEquiv1 n G).symm c : H1 G (ULift.{u} (ZMod n)))) :
        H1 G (ZMod n)) := by
  unfold h1EquivCohomFp
  simp

end Coefficients

end TauCeti
