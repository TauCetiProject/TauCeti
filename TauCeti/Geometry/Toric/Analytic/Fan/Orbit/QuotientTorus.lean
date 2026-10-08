/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Cone.Sublattice
public import TauCeti.Geometry.Toric.Analytic.Fan.Orbit.Basic
public import TauCeti.Geometry.Toric.Analytic.Torus.Topology

/-!
# Orbits of a toric fan as quotient tori

Let `σ` be a cone of a regular fan in a lattice `N`, and let `N_σ = coneSublattice i σ` be the
sublattice of lattice vectors in the real span of `σ`. The quotient `N(σ) = N ⧸ N_σ` is again a
lattice, and the quotient map induces a surjective homomorphism of complex tori
`T_N → T_{N(σ)}`. Its kernel is the stabilizer of the distinguished point of `σ`, by the
description of that stabilizer as the subtorus trivial on the characters vanishing on `σ`.

By the orbit–stabilizer theorem, the orbit of `σ` in the analytic realization is therefore
identified with the quotient torus `T_{N(σ)}`, the distinguished point corresponding to `1` and
the torus acting through `T_N → T_{N(σ)}`. In the chart of `σ`, every character `m` of `N(σ)`
vanishes on `σ`, so it lies in the dual semigroup of `σ`, and the identification sends a point of
the orbit to the torus point whose value at `m` is the value of the monomial of `m` at that point.
This formula shows that the identification is continuous; its inverse is continuous because a
section of the lattice map `N → N(σ)` gives a continuous section of `T_N → T_{N(σ)}`. So the orbit
of `σ`, with the subspace topology of the realization, is homeomorphic to `T_{N(σ)}`.

## Main declarations

* `TauCeti.Toric.complexTorusMap_mk'_coneSublattice_surjective`: the torus `T_N` surjects onto the
  quotient torus `T_{N(σ)}`.
* `TauCeti.Toric.Fan.stabilizer_analyticDistinguishedPoint`: the stabilizer of the distinguished
  point of `σ` is the kernel of `T_N → T_{N(σ)}`.
* `TauCeti.Toric.Fan.analyticConeOrbitTorusHomeomorph`: the orbit of `σ` is homeomorphic to the
  quotient torus `T_{N(σ)}`.
* `TauCeti.Toric.Fan.analyticConeOrbitTorusHomeomorph_smul`: the homeomorphism is equivariant
  along `T_N → T_{N(σ)}`.
* `TauCeti.Toric.Fan.val_analyticConeOrbitTorusHomeomorph_apply`: in the chart of `σ` it is
  given by evaluating the monomials of the characters of `N(σ)`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.2 and Lemma 3.2.5.
-/

public section

open Multiplicative Set Topology

namespace TauCeti.Toric

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- The torus of a finitely generated lattice `N` surjects onto the torus of the quotient lattice
`N ⧸ N_σ` of any cone `σ`: that quotient is torsion free, hence free. -/
theorem complexTorusMap_mk'_coneSublattice_surjective [Module.Finite ℤ N]
    (i : N →+ V) (σ : PointedCone ℝ V) :
    Function.Surjective (complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ))) :=
  complexTorusMap_surjective (QuotientAddGroup.mk'_surjective _)

namespace Fan

variable (Φ : Fan i) (hΦ : Φ.IsRegular)

/-- The stabilizer of the distinguished point of a cone `σ` is the kernel of the torus map
`T_N → T_{N(σ)}` induced by the quotient by the sublattice `N_σ` of `σ`. -/
theorem stabilizer_analyticDistinguishedPoint (σ : Φ.cones) :
    MulAction.stabilizer (ComplexTorus N) (Φ.analyticDistinguishedPoint hΦ σ) =
      (complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1))).ker := by
  ext T
  rw [mem_stabilizer_analyticDistinguishedPoint_iff, mem_ker_complexTorusMap_mk'_iff]
  exact forall_congr' fun m ↦ imp_congr_left
    ((Φ.isToricCone σ.2).rational.forall_realCharacter_eq_zero_iff_coneSublattice_le_ker
      Φ.lattice m)

/-- Pulling a character of `N ⧸ N_σ` back along the quotient map is composition with it. -/
private theorem compHom'_mk'_coneSublattice (σ : PointedCone ℝ V)
    (m : N ⧸ coneSublattice i σ →+ ℤ) :
    AddMonoidHom.compHom' (QuotientAddGroup.mk' (coneSublattice i σ)) m =
      m.comp (QuotientAddGroup.mk' (coneSublattice i σ)) :=
  AddMonoidHom.ext fun n ↦ AddMonoidHom.compHom'_apply_apply _ m n

/-- The orbit of `σ` identified with the quotient torus `T_{N(σ)}` by the orbit–stabilizer
theorem, before its topology is considered. -/
private noncomputable def analyticConeOrbitTorusEquiv (σ : Φ.cones) :
    Φ.analyticConeOrbit hΦ σ ≃ ComplexTorus (N ⧸ coneSublattice i σ.1) :=
  have := Φ.lattice.finite
  have : (MulAction.stabilizer (ComplexTorus N) (Φ.analyticDistinguishedPoint hΦ σ)).Normal :=
    Φ.stabilizer_analyticDistinguishedPoint hΦ σ ▸ inferInstance
  (Set.equivOfEq (Φ.analyticConeOrbit_eq_orbit hΦ σ)).trans <|
    (MulAction.orbitEquivQuotientStabilizer (ComplexTorus N)
      (Φ.analyticDistinguishedPoint hΦ σ)).trans <|
      (QuotientGroup.quotientMulEquivOfEq
        (Φ.stabilizer_analyticDistinguishedPoint hΦ σ)).toEquiv.trans
        (QuotientGroup.quotientKerEquivOfSurjective _
          (complexTorusMap_mk'_coneSublattice_surjective i σ.1)).toEquiv

private theorem analyticConeOrbitTorusEquiv_smul_analyticDistinguishedPoint (σ : Φ.cones)
    (T : ComplexTorus N) :
    Φ.analyticConeOrbitTorusEquiv hΦ σ
        ⟨T • Φ.analyticDistinguishedPoint hΦ σ,
          Φ.smul_mem_analyticConeOrbit hΦ T
            (Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ)⟩ =
      complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) T := by
  have h : MulAction.orbitEquivQuotientStabilizer (ComplexTorus N)
      (Φ.analyticDistinguishedPoint hΦ σ)
      ⟨T • Φ.analyticDistinguishedPoint hΦ σ, MulAction.mem_orbit _ T⟩ = (T : _ ⧸ _) := by
    rw [← Equiv.eq_symm_apply]
    exact Subtype.ext (MulAction.orbitEquivQuotientStabilizer_symm_apply _ _ T).symm
  simp only [analyticConeOrbitTorusEquiv, Equiv.trans_apply, Set.equivOfEq_apply, h]
  -- The first isomorphism theorem sends the class of `T` to its image, by definition.
  rfl

private theorem val_analyticConeOrbitTorusEquiv_apply (σ : Φ.cones)
    {y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)}
    (hy : y ∈ affineConeOrbit Φ.lattice (⊤ : σ.1.Face))
    (m : N ⧸ coneSublattice i σ.1 →+ ℤ) :
    ((Φ.analyticConeOrbitTorusEquiv hΦ σ
        ⟨Φ.analyticAffineChartι hΦ σ y,
          (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).2 rfl⟩ m : ℂˣ) : ℂ) =
      y (MonoidAlgebra.single (ofAdd ⟨m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1)),
        (Φ.isToricCone σ.2).rational.comp_mk'_mem_dualSemigroup Φ.lattice m⟩) 1) := by
  -- Write `y` as a torus translate of the distinguished point of the top face.
  obtain ⟨T, rfl⟩ : y ∈ MulAction.orbit (ComplexTorus N)
      (distinguishedPoint Φ.lattice (⊤ : σ.1.Face)) := by
    rwa [← affineConeOrbit_eq_orbit Φ.lattice ((isRegular_iff.mp hΦ) σ.1 σ.2)]
  dsimp only at hy ⊢
  have hι : Φ.analyticAffineChartι hΦ σ (T • distinguishedPoint Φ.lattice (⊤ : σ.1.Face)) =
      T • Φ.analyticDistinguishedPoint hΦ σ := by
    rw [analyticDistinguishedPoint_def]
    exact (Φ.smul_analyticAffineChartι hΦ T σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face))).symm
  have he : Φ.analyticConeOrbitTorusEquiv hΦ σ
      ⟨Φ.analyticAffineChartι hΦ σ (T • distinguishedPoint Φ.lattice (⊤ : σ.1.Face)),
        (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).2 rfl⟩ =
      complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) T := by
    rw [← Φ.analyticConeOrbitTorusEquiv_smul_analyticDistinguishedPoint hΦ σ T]
    exact congrArg _ (Subtype.ext hι)
  -- The character of `N(σ)` vanishes on `σ`, so its monomial is `1` at the distinguished point.
  have hvan : ∀ y, y ∈ (⊤ : σ.1.Face) →
      Φ.lattice.realCharacter (m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1))) y = 0 :=
    fun _ hy ↦ (Φ.isToricCone σ.2).rational.realCharacter_comp_mk'_eq_zero Φ.lattice m hy
  rw [he, AffineSemigroupComplexPoint.ambient_smul_apply_single, distinguishedPoint_apply_single]
  split_ifs with h
  · rw [mul_one, complexTorusMap_apply, characterEvaluation_apply, compHom'_mk'_coneSublattice]
  · exact absurd hvan h

/-- **Orbits are quotient tori.** The orbit of a cone `σ` of a regular fan, with the subspace
topology of the realization, is homeomorphic to the torus of the quotient lattice `N ⧸ N_σ`.
The distinguished point of `σ` corresponds to `1`, and the torus acts through the quotient map
(`analyticConeOrbitTorusHomeomorph_smul`). -/
noncomputable def analyticConeOrbitTorusHomeomorph (σ : Φ.cones) :
    Φ.analyticConeOrbit hΦ σ ≃ₜ ComplexTorus (N ⧸ coneSublattice i σ.1) where
  toEquiv := Φ.analyticConeOrbitTorusEquiv hΦ σ
  continuous_toFun := by
    -- Parametrize the orbit by the stratum of the top face in the chart of `σ`; there the
    -- identification evaluates monomials, which are continuous.
    let k := ((Φ.isOpenEmbedding_analyticAffineChartι hΦ σ).isEmbedding.homeomorphImage
      (affineConeOrbit Φ.lattice (⊤ : σ.1.Face))).trans
        (Homeomorph.setCongr (Φ.analyticConeOrbit_def hΦ σ).symm)
    have hmono (s : dualSemigroup Φ.lattice σ.1) :
        Continuous[(Φ.analyticAffineChart σ).str, inferInstance]
          fun y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) ↦
            y (MonoidAlgebra.single (ofAdd s) 1) := by
      have h := continuous_apply_single (Φ.analyticChartGenerators σ).2 s
      rwa [← Φ.analyticAffineChart_str_eq σ] at h
    have hval (m : N ⧸ coneSublattice i σ.1 →+ ℤ) :
        Continuous fun y ↦ ((Φ.analyticConeOrbitTorusEquiv hΦ σ (k y) m : ℂˣ) : ℂ) :=
      ((hmono _).comp continuous_subtype_val).congr fun y ↦
        (Φ.val_analyticConeOrbitTorusEquiv_apply hΦ σ y.2 m).symm
    rw [Equiv.toFun_as_coe, ← k.comp_continuous_iff']
    refine continuous_complexTorus_iff.2 fun m ↦ Units.continuous_iff.2 ⟨hval m, ?_⟩
    simpa only [Function.comp_apply, AddChar.map_neg_eq_inv] using hval (-m)
  continuous_invFun := by
    -- A section of the lattice map `N → N ⧸ N_σ` gives a continuous inverse.
    have := Φ.lattice.finite
    obtain ⟨g, hg⟩ := exists_complexTorusMap_comp_complexTorusMap_eq_id
      (QuotientAddGroup.mk'_surjective (coneSublattice i σ.1))
    have hsymm : ⇑(Φ.analyticConeOrbitTorusEquiv hΦ σ).symm = fun T ↦
        ⟨complexTorusMap g T • Φ.analyticDistinguishedPoint hΦ σ,
          Φ.smul_mem_analyticConeOrbit hΦ _
            (Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ)⟩ := by
      funext T
      rw [Equiv.symm_apply_eq, analyticConeOrbitTorusEquiv_smul_analyticDistinguishedPoint]
      exact (DFunLike.congr_fun hg T).symm
    rw [Equiv.invFun_as_coe, hsymm]
    exact ((continuous_complexTorusMap g).smul continuous_const).subtype_mk _

/-- In the chart of `σ`, the identification of the orbit of `σ` with the quotient torus evaluates
monomials: its value at a character `m` of `N ⧸ N_σ` is the value of the monomial of `m`, a
character of the dual semigroup of `σ`. -/
theorem val_analyticConeOrbitTorusHomeomorph_apply (σ : Φ.cones)
    {y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)}
    (hy : y ∈ affineConeOrbit Φ.lattice (⊤ : σ.1.Face))
    (m : N ⧸ coneSublattice i σ.1 →+ ℤ) :
    ((Φ.analyticConeOrbitTorusHomeomorph hΦ σ
        ⟨Φ.analyticAffineChartι hΦ σ y,
          (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hy).2 rfl⟩ m : ℂˣ) : ℂ) =
      y (MonoidAlgebra.single (ofAdd ⟨m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1)),
        (Φ.isToricCone σ.2).rational.comp_mk'_mem_dualSemigroup Φ.lattice m⟩) 1) :=
  Φ.val_analyticConeOrbitTorusEquiv_apply hΦ σ hy m

/-- The translate of the distinguished point of `σ` by a torus point `T` corresponds to the image
of `T` in the quotient torus. -/
@[simp]
theorem analyticConeOrbitTorusHomeomorph_smul_analyticDistinguishedPoint (σ : Φ.cones)
    (T : ComplexTorus N) :
    Φ.analyticConeOrbitTorusHomeomorph hΦ σ
        ⟨T • Φ.analyticDistinguishedPoint hΦ σ, Φ.smul_mem_analyticConeOrbit hΦ T
          (Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ)⟩ =
      complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) T :=
  Φ.analyticConeOrbitTorusEquiv_smul_analyticDistinguishedPoint hΦ σ T

/-- The inverse identification sends the image of a torus point `T` in the quotient torus to the
translate of the distinguished point of `σ` by `T`. -/
@[simp]
theorem coe_analyticConeOrbitTorusHomeomorph_symm_complexTorusMap (σ : Φ.cones)
    (T : ComplexTorus N) :
    ((Φ.analyticConeOrbitTorusHomeomorph hΦ σ).symm
        (complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) T) :
        Φ.analyticRealization hΦ) =
      T • Φ.analyticDistinguishedPoint hΦ σ := by
  rw [(Homeomorph.symm_apply_eq _).2
    (Φ.analyticConeOrbitTorusHomeomorph_smul_analyticDistinguishedPoint hΦ σ T).symm]

/-- The distinguished point of `σ` corresponds to the identity of the quotient torus. -/
@[simp]
theorem analyticConeOrbitTorusHomeomorph_analyticDistinguishedPoint (σ : Φ.cones) :
    Φ.analyticConeOrbitTorusHomeomorph hΦ σ
        ⟨Φ.analyticDistinguishedPoint hΦ σ,
          Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ⟩ = 1 := by
  -- Every monomial of a character of `N ⧸ N_σ` takes the value `1` at the distinguished point.
  refine DFunLike.ext _ _ fun m ↦ Units.ext ?_
  have hd := distinguishedPoint_mem_affineConeOrbit Φ.lattice (⊤ : σ.1.Face)
  have hvan : ∀ y, y ∈ (⊤ : σ.1.Face) →
      Φ.lattice.realCharacter (m.comp (QuotientAddGroup.mk' (coneSublattice i σ.1))) y = 0 :=
    fun _ hy ↦ (Φ.isToricCone σ.2).rational.realCharacter_comp_mk'_eq_zero Φ.lattice m hy
  have h := Φ.val_analyticConeOrbitTorusHomeomorph_apply hΦ σ hd m
  rw [distinguishedPoint_apply_single, ite_eq_left hvan] at h
  have hx₀ : (⟨Φ.analyticDistinguishedPoint hΦ σ,
      Φ.analyticDistinguishedPoint_mem_analyticConeOrbit hΦ σ⟩ : Φ.analyticConeOrbit hΦ σ) =
      ⟨Φ.analyticAffineChartι hΦ σ (distinguishedPoint Φ.lattice (⊤ : σ.1.Face)),
        (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hd).2 rfl⟩ :=
    Subtype.ext (Φ.analyticDistinguishedPoint_def hΦ σ)
  rw [hx₀, h, AddChar.one_apply, Units.val_one]

/-- The identification of the orbit of `σ` with the quotient torus is equivariant: translating by
a torus point `T` multiplies by the image of `T` in the quotient torus. -/
theorem analyticConeOrbitTorusHomeomorph_smul (σ : Φ.cones) (T : ComplexTorus N)
    (x : Φ.analyticConeOrbit hΦ σ) :
    Φ.analyticConeOrbitTorusHomeomorph hΦ σ ⟨T • x.1, Φ.smul_mem_analyticConeOrbit hΦ T x.2⟩ =
      complexTorusMap (QuotientAddGroup.mk' (coneSublattice i σ.1)) T *
        Φ.analyticConeOrbitTorusHomeomorph hΦ σ x := by
  -- Compute both sides on monomials in the chart of `σ`.
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ : ∃ y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1),
      y ∈ affineConeOrbit Φ.lattice (⊤ : σ.1.Face) ∧ Φ.analyticAffineChartι hΦ σ y = x := by
    rwa [analyticConeOrbit_def] at hx
  have hTy := (smul_mem_affineConeOrbit_iff Φ.lattice (⊤ : σ.1.Face) T).2 hy
  have hι : (⟨T • Φ.analyticAffineChartι hΦ σ y, Φ.smul_mem_analyticConeOrbit hΦ T hx⟩ :
      Φ.analyticConeOrbit hΦ σ) = ⟨Φ.analyticAffineChartι hΦ σ (T • y),
        (Φ.analyticAffineChartι_mem_analyticConeOrbit_iff hΦ hTy).2 rfl⟩ :=
    Subtype.ext (Φ.smul_analyticAffineChartι hΦ T σ y)
  refine DFunLike.ext _ _ fun m ↦ Units.ext ?_
  rw [hι, AddChar.mul_apply, Units.val_mul, Φ.val_analyticConeOrbitTorusHomeomorph_apply hΦ σ hy,
    Φ.val_analyticConeOrbitTorusHomeomorph_apply hΦ σ hTy,
    AffineSemigroupComplexPoint.ambient_smul_apply_single, complexTorusMap_apply,
    characterEvaluation_apply, compHom'_mk'_coneSublattice]

end Fan

end TauCeti.Toric
