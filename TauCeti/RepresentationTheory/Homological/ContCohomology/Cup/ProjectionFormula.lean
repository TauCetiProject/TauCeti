/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pairing
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.AllDegrees
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Functoriality

/-!
# The projection formula for continuous cohomology

For an open subgroup `U` of a profinite group `G` (so of finite index), a continuous equivariant
pairing `P : X × Y → Z` of topological representations over a commutative ring, and classes
`a ∈ Hᵐ(G, X)`, `b ∈ Hⁿ(U, Y)`, this file proves the projection formula in every bidegree when
`Y` and `Z` are smooth and discrete:

```text
cor (res a ⌣ b) = a ⌣ cor b.
```

The proof uses the definition of all-degree corestriction through Shapiro's lemma. The pairing
`TauCeti.coindTopPairing`, built from `TauCeti.DiscreteCoind.pairing`, sends `(x, f)` to the
coinduced function `g ↦ P(g • x, f g)`. Evaluation at `1` identifies its cup product under the
generic Shapiro map with `res a ⌣ b`, while the coefficient trace sends this function to
`P(x, tr f)`. Naturality of the all-degree cup product then gives the result.

## Main definitions

* `TauCeti.coindTopPairing`: the coefficient pairing
  `X × Coind_U^G Y → Coind_U^G Z` on smooth discrete topological representations.

## Main results

* `TauCeti.coindTopPairing_coindCounit`: the coinduction counit commutes with the pairing.
* `TauCeti.coindTopPairing_trace`, `TauCeti.coindTopPairing_coindTraceHom`: the trace commutes
  with the pairing.
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

/-- The bilinear map of a pairing as a biadditive map, the input of `DiscreteCoind.pairing`. -/
private def bilAddMonoidHom (P : TopPairing X Y Z) : X.V →+ Y.V →+ Z.V :=
  LinearMap.toAddMonoidHom'.comp P.bil.toAddMonoidHom

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
private theorem bilAddMonoidHom_apply (P : TopPairing X Y Z) (x : X.V) (y : Y.V) :
    bilAddMonoidHom P x y = P.bil x y := rfl

-- The actions `g • _` are the operators `X.ρ g`, `Y.ρ g`, `Z.ρ g` by definition of the local
-- instance `TopRep.distribMulAction`.
omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in
private theorem bilAddMonoidHom_smul (P : TopPairing X Y Z) (g : G) (x : X.V) (y : Y.V) :
    bilAddMonoidHom P (g • x) (g • y) = g • bilAddMonoidHom P x y :=
  P.equivariant g x y

omit [CompactSpace G] in
private theorem continuousSMul_subgroup (hZ : IsSmoothDiscrete R Z) : ContinuousSMul U Z.V :=
  let _ : ContinuousSMul G Z.V := hZ.continuousSMul
  inferInstance

/-- The underlying bilinear map of `coindTopPairing`: `DiscreteCoind.pairing` of the bilinear map
of `P`, which is `R`-linear in each variable. -/
private noncomputable def coindBil (hU : IsOpen (U : Set G))
    (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) :
    X.V →ₗ[R] DiscreteCoind G U Y.V →ₗ[R] DiscreteCoind G U Z.V :=
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul U Z.V := continuousSMul_subgroup U hZ
  LinearMap.mk₂ R (DiscreteCoind.pairing U hU (bilAddMonoidHom P) (bilAddMonoidHom_smul P) · ·)
    (fun x x' f ↦ by rw [map_add, AddMonoidHom.add_apply])
    (fun r x f ↦ DiscreteCoind.ext fun g ↦ by
      simp [DiscreteCoind.pairing_apply, smul_comm g r x])
    (fun x f f' ↦ map_add _ f f')
    (fun r x f ↦ DiscreteCoind.ext fun g ↦ by simp [DiscreteCoind.pairing_apply])

omit [CompactSpace G] in
private theorem coindBil_apply (hU : IsOpen (U : Set G))
    (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) (x : X.V)
    (f : DiscreteCoind G U Y.V) (g : G) :
    coindBil U hU hZ P x f g = P.bil (X.ρ g x) (f g) :=
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul U Z.V := continuousSMul_subgroup U hZ
  DiscreteCoind.pairing_apply U hU (bilAddMonoidHom P) (bilAddMonoidHom_smul P) x f g

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
    simpa only [coindBil_apply] using hp'
  refine ⟨W, ?_, hW, hpW⟩
  intro p' hp'
  rcases hp' with ⟨hp'V, hp'2⟩
  have hp'2eq : p'.2 = p.2 := by simpa using hp'2
  -- The goal is membership of `coindBil U hU hZ P p'.1 p'.2` in the singleton `{q}`.
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
  simpa only [coindBil_apply] using congrArg (u • ·) (hp'V' (QuotientGroup.mk g⁻¹))

/-- The pairing `X × Coind Y → Coind Z`, `(x, f) ↦ (g ↦ P (g • x) (f g))`, induced by a continuous
equivariant pairing `P : X × Y → Z`, for smooth discrete `Y` and `Z`. It is
`DiscreteCoind.pairing` of the bilinear map of `P`. -/
noncomputable def coindTopPairing (hU : IsOpen (U : Set G))
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z) :
    TopPairing X
      (coindTopRep R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩)).obj
      (coindTopRep R G U (smoothDiscreteResTopRep U ⟨Z, hZ⟩)).obj :=
  haveI : Finite (G ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul U Z.V := continuousSMul_subgroup U hZ
  { bil := coindBil U hU hZ P
    cont := coindBil_continuous U hU hY hZ P
    -- The action of `G` on the coinduced representation is the translation action on
    -- `DiscreteCoind G U Y.V`.
    equivariant g x f := DiscreteCoind.pairing_smul U hU _ (bilAddMonoidHom_smul P) g x f }

@[simp]
theorem coindTopPairing_bil_apply (hU : IsOpen (U : Set G))
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (x : X.V) (f : DiscreteCoind G U Y.V) (g : G) :
    (show DiscreteCoind G U Z.V from (coindTopPairing U hU hY hZ P).bil x f) g =
      P.bil (X.ρ g x) (f g) :=
  coindBil_apply U hU hZ P x f g

-- Not `@[simp]`: the left-hand side is unfolded by the simp lemma `DiscreteCoind.trace_apply`.
/-- **The trace commutes with the coinduced pairing**: `tr (x ⋆ f) = P (x, tr f)`. -/
theorem coindTopPairing_trace (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (x : X.V) (f : DiscreteCoind G U Y.V) :
    DiscreteCoind.trace G U Z.V ((coindTopPairing U hU hY hZ P).bil x f) =
      P.bil x (DiscreteCoind.trace G U Y.V f) :=
  let _ : DiscreteTopology Z.V := hZ.discreteTopology
  let _ : ContinuousSMul U Z.V := continuousSMul_subgroup U hZ
  DiscreteCoind.trace_pairing U hU (bilAddMonoidHom P) (bilAddMonoidHom_smul P) x f

-- Not `@[simp]`: the left-hand side is unfolded by the simp lemma `coindTraceHom_apply`.
/-- The trace law of `coindTopPairing`, stated with the trace morphism `coindTraceHom`. -/
theorem coindTopPairing_coindTraceHom (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    (Y₀ Z₀ : SmoothDiscreteTopRep.{u, v, v} R G) (P : TopPairing X Y₀.obj Z₀.obj)
    (x : X.V) (f : DiscreteCoind G U Y₀.obj.V) :
    (coindTraceHom R G U Z₀) ((coindTopPairing U hU Y₀.property Z₀.property P).bil x f) =
      P.bil x ((coindTraceHom R G U Y₀) f) := by
  -- `coindTraceHom_apply` does not rewrite here: its domain is the restricted object written
  -- out, which only matches `smoothDiscreteResTopRep` up to unfolding.
  exact (coindTraceHom_apply R G U Z₀ _).trans
    ((coindTopPairing_trace U hU Y₀.property Z₀.property P x f).trans
      (congrArg (P.bil x) (coindTraceHom_apply R G U Y₀ f).symm))

-- Not `@[simp]`: the left-hand side is unfolded by the simp lemma `coindCounit_apply`.
/-- **The coinduction counit commutes with the coinduced pairing**: evaluating `x ⋆ f` at `1`
gives `P (x, f 1)`. -/
theorem coindTopPairing_coindCounit (hU : IsOpen (U : Set G))
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (x : X.V) (f : DiscreteCoind G U Y.V) :
    (coindCounit R G U (smoothDiscreteResTopRep U ⟨Z, hZ⟩))
        ((coindTopPairing U hU hY hZ P).bil x f) =
      P.bil x ((coindCounit R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩)) f) := by
  refine (coindCounit_apply R G U _ _).trans <|
    (coindTopPairing_bil_apply U hU hY hZ P x f 1).trans ?_
  have hy := coindCounit_apply R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩) f
  rw [map_one, hy]
  rfl

namespace TopPairing

private theorem coindTopPairing_counit (hU : IsOpen (U : Set G))
    (hY : IsSmoothDiscrete R Y) (hZ : IsSmoothDiscrete R Z) (P : TopPairing X Y Z)
    (Pres : TopPairing (TopRep.res (U.subtype : U →* G) X)
      (TopRep.res (U.subtype : U →* G) Y) (TopRep.res (U.subtype : U →* G) Z))
    (hPres : Pres.bil = P.bil) (x : X.V) (f : DiscreteCoind G U Y.V) :
    (coindCounit R G U (smoothDiscreteResTopRep U ⟨Z, hZ⟩))
        ((coindTopPairing U hU hY hZ P).bil x f) =
      Pres.bil x ((coindCounit R G U (smoothDiscreteResTopRep U ⟨Y, hY⟩)) f) := by
  rw [coindTopPairing_coindCounit, hPres]

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
    -- `subgroupSubtype U` coerces to `U.subtype` definitionally, so the two restrictions of `X`
    -- are the same object and `fX` is the identity.
    let fX : TopRep.res (ContinuousMonoidHom.subgroupSubtype U : U →* G) X ⟶
        TopRep.res (U.subtype : U →* G) X := eqToHom (by rfl)
    have h := Q.cup_map Pres (ContinuousMonoidHom.subgroupSubtype U) fX
      (TopRep.ofHom (coindCounit R G U AY)) (TopRep.ofHom (coindCounit R G U AZ))
      hcompat m n a b
    have hfX : fX = 𝟙 (TopRep.res (U.subtype : U →* G) X) := by rfl
    rw [hfX] at h
    simpa only [ContinuousCohomology.shapiroMapTopRep_def,
      ContinuousCohomology.res_def, fX] using h

omit [CompactSpace G] in
private theorem cup_coeffMap_left_id {Y' Z' : TopRep.{v} R G}
    (Q : TopPairing X Y' Z') (P : TopPairing X Y Z) (fY : Y' ⟶ Y) (fZ : Z' ⟶ Z)
    (hcompat : ∀ (x : X.V) (y : Y'.V), fZ (Q.bil x y) = P.bil x (fY y))
    (m n : ℕ) (a : continuousCohomology m X) (b : continuousCohomology n Y') :
    ContinuousCohomology.coeffMap fZ (m + n) (Q.cup m n a b) =
      P.cup m n a (ContinuousCohomology.coeffMap fY n b) := by
  have h := Q.cup_coeffMap P (𝟙 X) fY fZ (fun x y ↦ by
    -- `𝟙 X` acts on elements as the identity.
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
  rw [ContinuousCohomology.corestrictionTopRep_def, ConcreteCategory.comp_apply]

/-- **The projection formula in every bidegree** for a continuous pairing over an arbitrary
commutative coefficient ring, with smooth discrete source and target coefficients. -/
theorem cup_projection [TotallyDisconnectedSpace G]
    (hU : IsOpen (U : Set G))
    (Y₀ Z₀ : SmoothDiscreteTopRep.{u, v, v} R G) (P : TopPairing X Y₀.obj Z₀.obj)
    (Pres : TopPairing (TopRep.res (U.subtype : U →* G) X)
      (TopRep.res (U.subtype : U →* G) Y₀.obj)
      (TopRep.res (U.subtype : U →* G) Z₀.obj))
    (hPres : Pres.bil = P.bil) (m n : ℕ) (a : continuousCohomology m X)
    (b : continuousCohomology n (TopRep.res (U.subtype : U →* G) Y₀.obj)) :
    ContinuousCohomology.corestrictionTopRep U Z₀ hU (m + n)
        (Pres.cup m n (ContinuousCohomology.res U X m a) b) =
      P.cup m n a (ContinuousCohomology.corestrictionTopRep U Y₀ hU n b) := by
  have : Finite (G ⧸ U) := U.quotient_finite_of_isOpen hU
  have : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact cup_projection_of_compatible U hU Y₀ Z₀ P Pres
    (coindTopPairing U hU Y₀.property Z₀.property P)
    (coindTopPairing_counit U hU Y₀.property Z₀.property P Pres hPres)
    (coindTopPairing_coindTraceHom U hU Y₀ Z₀ P) m n a b

end TopPairing

end TauCeti
