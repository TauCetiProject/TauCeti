/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# The projection formula for continuous cohomology

For an open finite-index subgroup `U` of a profinite group `G`, a continuous equivariant pairing
`P : X × Y → Z` of topological representations over a commutative ring, and classes
`a ∈ Hᵐ(G, X)`, `b ∈ Hⁿ(U, Y)`, this file proves the projection formula in every bidegree when
`Y` and `Z` are smooth and discrete:

```text
cor (res a ⌣ b) = a ⌣ cor b.
```

The proof uses the definition of all-degree corestriction through Shapiro's lemma. The pairing
`TauCeti.coindTopPairing` sends `(m, f)` to the coinduced function
`g ↦ P(g • x, f g)`. Evaluation at `1` identifies its cup product under the generic Shapiro map
with `res a ⌣ b`, while the coefficient trace sends this function to `P(x, tr f)`. Naturality of
the all-degree cup product then gives the result.

## Main definitions

* `TauCeti.coindTopPairing`: the coefficient pairing
  `X × Coind_U^G Y → Coind_U^G Z` on smooth discrete topological representations.

## Main results

* `TauCeti.TopPairing.cup_projection`: **the projection formula in every bidegree**.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer (1982), Chapter V, §3, (3.8).
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter I, §5, (1.5.3)(iv).
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology _root_.ContinuousCohomology

universe u v

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G) {X Y Z : TopRep.{v} R G}

omit [CompactSpace G] in
private theorem locallyConstant_of_equivariant (hU : IsOpen (U : Set G))
    (hZ : IsSmoothDiscrete R Z) (k : G → Z.V)
    (hk : ∀ (u : U) (g : G), k (u * g) = u • k g) : IsLocallyConstant k := by
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul G Z.V := hZ.continuousSMul
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  let S : Set U := MulAction.stabilizer U (k g)
  have hS : IsOpen S := stabilizer_isOpen U (k g)
  have hopen : IsOpen ((fun u : U ↦ (u : G) * g) '' S) :=
    ((isOpenMap_mul_right g).comp hU.isOpenMap_subtype_val) S hS
  have hg : g ∈ (fun u : U ↦ (u : G) * g) '' S := by
    refine ⟨1, ?_, by simp⟩
    simp [S]
  filter_upwards [hopen.mem_nhds hg] with x hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [hk]
  exact hu

private noncomputable def coindValue (hU : IsOpen (U : Set G))
    (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) (x : X.V)
    (f : DiscreteCoind G U Y.V) : DiscreteCoind G U Z.V :=
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul G Z.V := hZ.continuousSMul
  DiscreteCoind.mk G U Z.V (fun g ↦ P.bil (X.ρ g x) (f g))
      (locallyConstant_of_equivariant U hU hZ _ fun u g ↦ by
        rw [f.apply_mul]
        change P.bil (X.ρ ((u : G) * g) x) (Y.ρ (u : G) (f g)) =
          Z.ρ (u : G) (P.bil (X.ρ g x) (f g))
        have hrho : X.ρ ((u : G) * g) x = X.ρ (u : G) (X.ρ g x) := by
          change ((u : G) * g) • x = (u : G) • g • x
          exact mul_smul (u : G) g x
        rw [hrho]
        exact P.equivariant (u : G) (X.ρ g x) (f g))
      fun u g ↦ by
        rw [f.apply_mul]
        change P.bil (X.ρ ((u : G) * g) x) (Y.ρ (u : G) (f g)) =
          Z.ρ (u : G) (P.bil (X.ρ g x) (f g))
        have hrho : X.ρ ((u : G) * g) x = X.ρ (u : G) (X.ρ g x) := by
          change ((u : G) * g) • x = (u : G) • g • x
          exact mul_smul (u : G) g x
        rw [hrho]
        exact P.equivariant (u : G) (X.ρ g x) (f g)

omit [CompactSpace G] in
@[simp]
private theorem coindValue_apply (hU : IsOpen (U : Set G))
    (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) (x : X.V)
    (f : DiscreteCoind G U Y.V) (g : G) :
    coindValue U hU hZ P x f g = P.bil (X.ρ g x) (f g) := rfl

private noncomputable def coindBil (hU : IsOpen (U : Set G))
    (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) :
    X.V →ₗ[R] DiscreteCoind G U Y.V →ₗ[R] DiscreteCoind G U Z.V :=
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul G Z.V := hZ.continuousSMul
  LinearMap.mk₂ R (coindValue U hU hZ P)
      (fun x x' f ↦ DiscreteCoind.ext fun g ↦ by
        change P.bil (X.ρ g (x + x')) (f g) =
          P.bil (X.ρ g x) (f g) + P.bil (X.ρ g x') (f g)
        simp)
      (fun r x f ↦ DiscreteCoind.ext fun g ↦ by
        change P.bil (X.ρ g (r • x)) (f g) = r • P.bil (X.ρ g x) (f g)
        simp)
      (fun x f f' ↦ DiscreteCoind.ext fun g ↦ by
        change P.bil (X.ρ g x) ((f + f') g) =
          P.bil (X.ρ g x) (f g) + P.bil (X.ρ g x) (f' g)
        simp)
      (fun r x f ↦ DiscreteCoind.ext fun g ↦ by
        change P.bil (X.ρ g x) ((r • f) g) = r • P.bil (X.ρ g x) (f g)
        simp)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [CompactSpace G] in
private theorem coindBil_continuous (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) :
    Continuous fun p : X.V × DiscreteCoind G U Y.V ↦ coindBil U hU hZ P p.1 p.2 := by
  let _ : DiscreteTopology Y.V := hY.discreteTopology
  let _ : ContinuousSMul G Y.V := hY.continuousSMul
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul G Z.V := hZ.continuousSMul
  rw [continuous_discrete_rng]
  intro q
  rw [isOpen_iff_forall_mem_open]
  intro p hp
  have hpEq : coindBil U hU hZ P p.1 p.2 = q := by simpa using hp
  let V : Set X.V := ⋂ c : G ⧸ U,
    {x | P.bil (X.ρ c.out⁻¹ x) (p.2 c.out⁻¹) = q c.out⁻¹}
  have hV : IsOpen V := isOpen_iInter_of_finite fun c ↦
    (isOpen_discrete {q c.out⁻¹}).preimage
      (P.cont.comp ((X.ρ c.out⁻¹).continuous.prodMk continuous_const))
  let W : Set (X.V × DiscreteCoind G U Y.V) := V ×ˢ {p.2}
  have hW : IsOpen W := hV.prod (isOpen_discrete {p.2})
  have hpW : p ∈ W := by
    refine ⟨?_, rfl⟩
    simp only [V, Set.mem_iInter, Set.mem_ofPred_eq]
    intro c
    have hp' := congrArg (fun z : DiscreteCoind G U Z.V ↦ z c.out⁻¹) hpEq
    simpa only [coindBil, LinearMap.mk₂_apply, coindValue_apply] using hp'
  refine ⟨W, ?_, hW, hpW⟩
  intro p' hp'
  rcases hp' with ⟨hp'V, hp'2⟩
  have hp'2eq : p'.2 = p.2 := by simpa using hp'2
  change coindBil U hU hZ P p'.1 p'.2 = q
  rw [hp'2eq]
  apply DiscreteCoind.ext
  intro g
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g⁻¹
  have hg : g = (u : G) * ((QuotientGroup.mk g⁻¹ : G ⧸ U).out)⁻¹ := by
    rw [hu, mul_inv_rev, inv_inv]
    exact (mul_inv_cancel_left (u : G) g).symm
  rw [hg, DiscreteCoind.apply_mul, DiscreteCoind.apply_mul]
  have hp'V' : ∀ c : G ⧸ U,
      P.bil (X.ρ c.out⁻¹ p'.1) (p.2 c.out⁻¹) = q c.out⁻¹ := by
    simpa only [V, Set.mem_iInter, Set.mem_ofPred_eq] using hp'V
  exact congrArg (u • ·) (hp'V' (QuotientGroup.mk g⁻¹))

/-- The pairing `X × Coind Y → Coind Z` induced by a continuous equivariant pairing
`X × Y → Z`, for smooth discrete `Y` and `Z`. -/
noncomputable def coindTopPairing (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) :
    TopPairing X
      (coindTopRep R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩)).obj
      (coindTopRep R G U (smoothDiscreteResTopRep U ⟨Z, hZ⟩)).obj where
  bil := coindBil U hU hZ P
  cont := coindBil_continuous U hU hY hZ P
  equivariant g x f := DiscreteCoind.ext fun q ↦ by
    change P.bil (X.ρ q (X.ρ g x))
        ((show DiscreteCoind G U Y.V from f) (q * g)) =
      P.bil (X.ρ (q * g) x) ((show DiscreteCoind G U Y.V from f) (q * g))
    have hrho : X.ρ (q * g) x = X.ρ q (X.ρ g x) := by
      change (q * g) • x = q • g • x
      exact mul_smul q g x
    rw [hrho]

@[simp]
theorem coindTopPairing_bil_apply (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (x : X.V) (f : DiscreteCoind G U Y.V) (g : G) :
    (show DiscreteCoind G U Z.V from (coindTopPairing U hU hY hZ P).bil x f) g =
      P.bil (X.ρ g x) (f g) := by
  change coindValue U hU hZ P x f g = _
  exact coindValue_apply U hU hZ P x f g

private theorem coindTopPairing_trace (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (x : X.V) (f : DiscreteCoind G U Y.V) :
    DiscreteCoind.trace G U Z.V ((coindTopPairing U hU hY hZ P).bil x f) =
      P.bil x (DiscreteCoind.trace G U Y.V f) := by
  let _ : DiscreteTopology Y.V := hY.discreteTopology
  let _ : ContinuousSMul G Y.V := hY.continuousSMul
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul G Z.V := hZ.continuousSMul
  let qf : DiscreteCoind G U Z.V := (coindTopPairing U hU hY hZ P).bil x f
  change DiscreteCoind.trace G U Z.V qf = P.bil x (DiscreteCoind.trace G U Y.V f)
  rw [DiscreteCoind.trace_apply, DiscreteCoind.trace_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  change Z.ρ c.out (qf c.out⁻¹) = P.bil x (Y.ρ c.out (f c.out⁻¹))
  rw [show qf c.out⁻¹ = P.bil (X.ρ c.out⁻¹ x) (f c.out⁻¹) by
    exact coindTopPairing_bil_apply U hU hY hZ P x f c.out⁻¹]
  rw [← P.equivariant c.out (X.ρ c.out⁻¹ x) (f c.out⁻¹)]
  have hrho : X.ρ c.out (X.ρ c.out⁻¹ x) = x := by
    change c.out • c.out⁻¹ • x = x
    rw [← mul_smul, mul_inv_cancel, one_smul]
  rw [hrho]

private theorem coindTopPairing_trace_hom (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (Y₀ Z₀ : SmoothDiscreteTopRep.{u, v, v} R G) (P : TopPairing X Y₀.obj Z₀.obj)
    (x : X.V) (f : DiscreteCoind G U Y₀.obj.V) :
    (coindTraceHom R G U Z₀) ((coindTopPairing U hU Y₀.property Z₀.property P).bil x f) =
      P.bil x ((coindTraceHom R G U Y₀) f) := by
  let qz : DiscreteCoind G U Z₀.obj.V :=
    (coindTopPairing U hU Y₀.property Z₀.property P).bil x f
  have hz := coindTraceHom_apply R G U Z₀ qz
  have hy := coindTraceHom_apply R G U Y₀ f
  exact hz.trans ((coindTopPairing_trace U hU Y₀.property Z₀.property P x f).trans
    (congrArg (P.bil x) hy.symm))

namespace TopPairing

private theorem coindTopPairing_counit (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (Pres : TopPairing (TopRep.res (U.subtype : U →* G) X)
      (TopRep.res (U.subtype : U →* G) Y) (TopRep.res (U.subtype : U →* G) Z))
    (hPres : Pres.bil = P.bil) (x : X.V) (f : DiscreteCoind G U Y.V) :
    (coindCounit R G U (smoothDiscreteResTopRep U ⟨Z, hZ⟩))
        ((coindTopPairing U hU hY hZ P).bil x f) =
      Pres.bil x ((coindCounit R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩)) f) := by
  let qz : DiscreteCoind G U Z.V := (coindTopPairing U hU hY hZ P).bil x f
  have hz := coindCounit_apply R G U (smoothDiscreteResTopRep U ⟨Z, hZ⟩) qz
  have hy := coindCounit_apply R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩) f
  have hrho : X.ρ 1 x = x := by
    change (1 : G) • x = x
    exact one_smul G x
  refine hz.trans ((coindTopPairing_bil_apply U hU hY hZ P x f 1).trans ?_)
  rw [hrho, hPres, hy]
  rfl

private theorem shapiroMapTopRep_cup_of_compatible
    (AY AZ : SmoothDiscreteTopRep.{u, v, v} R U)
    (Q : TopPairing X (coindTopRep R G U AY).obj (coindTopRep R G U AZ).obj)
    (Pres : TopPairing (TopRep.res (U.subtype : U →* G) X) AY.obj AZ.obj)
    (hcompat : ∀ (x : X.V) (f : DiscreteCoind G U AY.obj.V),
      (TopRep.ofHom (coindCounit R G U AZ)) (Q.bil x f) =
        Pres.bil x ((TopRep.ofHom (coindCounit R G U AY)) f))
    (m n : ℕ) (a : continuousCohomology m X)
    (b : continuousCohomology n (coindTopRep R G U AY).obj) :
    ContinuousCohomology.shapiroMapTopRep U AZ (m + n) (Q.cup m n a b) =
      Pres.cup m n (ContinuousCohomology.res U X m a)
        (ContinuousCohomology.shapiroMapTopRep U AY n b) :=
  by
    let fX : TopRep.res (ContinuousMonoidHom.subgroupSubtype U : U →* G) X ⟶
        TopRep.res (U.subtype : U →* G) X := eqToHom (by rfl)
    have h := Q.cup_map Pres (ContinuousMonoidHom.subgroupSubtype U) fX
      (TopRep.ofHom (coindCounit R G U AY)) (TopRep.ofHom (coindCounit R G U AZ))
      hcompat m n a b
    have hfX : fX = 𝟙 (TopRep.res (U.subtype : U →* G) X) := by rfl
    rw [hfX] at h
    simpa only [ContinuousCohomology.shapiroMapTopRep,
      ContinuousCohomology.res_def, fX] using h

omit [CompactSpace G] in
private theorem cup_coeffMap_left_id {Y' Z' : TopRep.{v} R G}
    (Q : TopPairing X Y' Z') (P : TopPairing X Y Z) (fY : Y' ⟶ Y) (fZ : Z' ⟶ Z)
    (hcompat : ∀ (x : X.V) (y : Y'.V), fZ (Q.bil x y) = P.bil x (fY y))
    (m n : ℕ) (a : continuousCohomology m X) (b : continuousCohomology n Y') :
    ContinuousCohomology.coeffMap fZ (m + n) (Q.cup m n a b) =
      P.cup m n a (ContinuousCohomology.coeffMap fY n b) := by
  have h := Q.cup_coeffMap P (𝟙 X) fY fZ (fun x y ↦ by
    change fZ (Q.bil x y) = P.bil x (fY y)
    exact hcompat x y) m n a b
  rw [ContinuousCohomology.coeffMap_id] at h
  exact h

private theorem cup_projection_of_compatible [TotallyDisconnectedSpace G]
    (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (Y₀ Z₀ : SmoothDiscreteTopRep.{u, v, v} R G) (P : TopPairing X Y₀.obj Z₀.obj)
    (Pres : TopPairing (TopRep.res (U.subtype : U →* G) X)
      (TopRep.res (U.subtype : U →* G) Y₀.obj)
      (TopRep.res (U.subtype : U →* G) Z₀.obj))
    (Q : TopPairing X (coindTopRep R G U (smoothDiscreteResTopRep U Y₀)).obj
      (coindTopRep R G U (smoothDiscreteResTopRep U Z₀)).obj)
    (hpair : ∀ (x : X.V) (f : DiscreteCoind G U Y₀.obj.V),
      (TopRep.ofHom (coindCounit R G U (smoothDiscreteResTopRep U Z₀))) (Q.bil x f) =
        Pres.bil x ((TopRep.ofHom
          (coindCounit R G U (smoothDiscreteResTopRep U Y₀))) f))
    (htrace : ∀ (x : X.V) (f : DiscreteCoind G U Y₀.obj.V),
      (coindTraceHom R G U Z₀) (Q.bil x f) =
        P.bil x ((coindTraceHom R G U Y₀) f))
    (m n : ℕ) (a : continuousCohomology m X)
    (b : continuousCohomology n (TopRep.res (U.subtype : U →* G) Y₀.obj)) :
    ContinuousCohomology.corestrictionTopRep U Z₀ hU (m + n)
        (Pres.cup m n (ContinuousCohomology.res U X m a) b) =
      P.cup m n a (ContinuousCohomology.corestrictionTopRep U Y₀ hU n b) := by
  let AY := smoothDiscreteResTopRep U Y₀
  let b' := (ContinuousCohomology.shapiroIsoTopRep U
    (U.isClosed_of_isOpen hU) AY n).inv b
  refine (congrArg (ContinuousCohomology.corestrictionTopRep U Z₀ hU (m + n))
    ((shapiroMapTopRep_cup_of_compatible U _ _ Q Pres hpair m n a b').trans
      (congrArg (Pres.cup m n (ContinuousCohomology.res U X m a))
        (ContinuousCohomology.shapiroMapTopRep_shapiroIsoTopRep_inv_apply U
          (U.isClosed_of_isOpen hU) AY n b))).symm).trans ?_
  refine (ContinuousCohomology.corestrictionTopRep_shapiroMapTopRep_apply
    U Z₀ hU (m + n) (Q.cup m n a b')).trans ?_
  refine (cup_coeffMap_left_id Q P (coindTraceHom R G U Y₀)
    (coindTraceHom R G U Z₀) htrace m n a b').trans ?_
  apply congrArg (P.cup m n a)
  rw [ContinuousCohomology.corestrictionTopRep, ConcreteCategory.comp_apply]

/-- **The projection formula in every bidegree** for a continuous pairing over an arbitrary
commutative coefficient ring, with smooth discrete source and target coefficients. -/
theorem cup_projection [TotallyDisconnectedSpace G]
    (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (Y₀ Z₀ : SmoothDiscreteTopRep.{u, v, v} R G) (P : TopPairing X Y₀.obj Z₀.obj)
    (Pres : TopPairing (TopRep.res (U.subtype : U →* G) X)
      (TopRep.res (U.subtype : U →* G) Y₀.obj)
      (TopRep.res (U.subtype : U →* G) Z₀.obj))
    (hPres : Pres.bil = P.bil) (m n : ℕ) (a : continuousCohomology m X)
    (b : continuousCohomology n (TopRep.res (U.subtype : U →* G) Y₀.obj)) :
    ContinuousCohomology.corestrictionTopRep U Z₀ hU (m + n)
        (Pres.cup m n (ContinuousCohomology.res U X m a) b) =
      P.cup m n a (ContinuousCohomology.corestrictionTopRep U Y₀ hU n b) := by
  let Q := coindTopPairing U hU Y₀.property Z₀.property P
  exact cup_projection_of_compatible U hU Y₀ Z₀ P Pres Q
    (coindTopPairing_counit U hU Y₀.property Z₀.property P Pres hPres)
    (coindTopPairing_trace_hom U hU Y₀ Z₀ P) m n a b

end TopPairing

end TauCeti
