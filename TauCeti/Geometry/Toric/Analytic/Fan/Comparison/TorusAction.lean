/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.TorusAction.Coaction
public import TauCeti.Geometry.Toric.Analytic.Fan.Boundary.Basic
public import TauCeti.Geometry.Toric.Analytic.Fan.Character
public import TauCeti.Geometry.Toric.Analytic.Fan.Compact
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Torus
public import TauCeti.Geometry.Toric.Analytic.Fan.TorusAction.Holomorphic

/-!
# Torus action and character naturality of the algebraic–analytic toric comparison

The coordinate-free complex torus `ComplexTorus N` acts on the affine complex points of each cone
through the algebraic coordinate-ring coaction (`TauCeti.Toric.affineCoordinateRingCoaction_eval`).
Because face localizations are equivariant for this coaction, the affine actions glue to a
continuous torus action on the complex points `Φ.AlgebraicComplexPoint` of the toric scheme of any
finite fan `Φ`, without assuming regularity.

For a regular fan, the chartwise algebraic–analytic comparison `algebraicAnalyticEquiv` is the
identity on every affine chart, so it is torus-equivariant. Moreover:

* toric maps of algebraic complex points are equivariant for the torus homomorphism induced by the
  lattice map, and on the canonical dense torus inclusion they agree with that homomorphism;
* global character functions on algebraic complex points agree with `analyticCharacter` through the
  comparison, transform by their character under torus translation, and pull back along fan
  morphisms by precomposing with the lattice map;
* for a nonempty regular fan, compactness of `Φ.AlgebraicComplexPoint` is equivalent to
  completeness of `Φ`.

## Main declarations

* `TauCeti.Toric.Fan.AlgebraicComplexPoint.instMulActionComplexTorus`: the glued torus action on
  the complex points of the toric scheme of a fan.
* `TauCeti.Toric.Fan.continuousSMul_algebraicComplexPoint` and
  `TauCeti.Toric.Fan.contMDiffSMul_complexTorus_algebraicComplexPoint`: joint continuity and
  holomorphy of the torus action on algebraic complex points of a regular fan.
* `TauCeti.Toric.Fan.algebraicAnalyticEquiv_smul` and
  `TauCeti.Toric.Fan.algebraicAnalyticEquiv_symm_smul`: torus equivariance of the
  algebraic–analytic comparison.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.torusι`: the canonical dense-torus inclusion into the
  complex points of a nonempty fan scheme, intertwined with `analyticTorusι` by
  `TauCeti.Toric.Fan.algebraicAnalyticEquiv_torusι`.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.character`: the global character function on algebraic
  complex points, holomorphic on regular fans and intertwined with `analyticCharacter` by
  `TauCeti.Toric.Fan.analyticCharacter_algebraicAnalyticEquiv`.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.coneOrbit` and
  `TauCeti.Toric.Fan.AlgebraicComplexPoint.boundaryComponent`: the orbit strata and ray-indexed
  boundary components on algebraic complex points, matched with their analytic counterparts by
  `TauCeti.Toric.Fan.image_algebraicAnalyticEquiv_coneOrbit` and
  `TauCeti.Toric.Fan.image_algebraicAnalyticEquiv_boundaryComponent`.
* `TauCeti.Toric.Fan.compactSpace_algebraicComplexPoint_iff_isComplete`: for a nonempty regular
  fan, compactness of `Φ.AlgebraicComplexPoint` is equivalent to completeness of `Φ`.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3–1.4, 2.1 and 2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1, 3.1 and 3.4.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

namespace Fan

variable (Φ : Fan i)

namespace AlgebraicComplexPoint

variable {Φ}

/-- Equal representatives in two affine charts remain equal after torus translation. -/
private theorem ofAffinePoint_smul_eq_of_eq {σ τ : Φ.cones}
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
    (y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice τ.1))
    (t : ComplexTorus N) (h : ofAffinePoint σ x = ofAffinePoint τ y) :
    ofAffinePoint σ (t • x) = ofAffinePoint τ (t • y) := by
  obtain ⟨z, rfl, rfl⟩ := (ofAffinePoint_eq_ofAffinePoint_iff x y).1 h
  refine (ofAffinePoint_eq_ofAffinePoint_iff _ _).2 ⟨t • z, ?_, ?_⟩
  · exact faceAffinePointMap_smul Φ.lattice (Φ.inf_isFaceOf_left σ.2 τ.2) t z
  · exact faceAffinePointMap_smul Φ.lattice (Φ.inf_isFaceOf_right σ.2 τ.2) t z

/-- The coordinate-free complex torus acts on the complex points of the toric scheme of a fan by
translating affine chart representatives. -/
noncomputable instance : SMul (ComplexTorus N) Φ.AlgebraicComplexPoint where
  smul t p :=
    let h := exists_ofAffinePoint_eq p
    ofAffinePoint h.choose (t • h.choose_spec.choose)

/-- Every affine chart inclusion into the complex points of the toric scheme is equivariant for
the coordinate-free complex torus. -/
@[simp]
theorem smul_ofAffinePoint (t : ComplexTorus N) (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    t • ofAffinePoint σ x = ofAffinePoint σ (t • x) := by
  let h := exists_ofAffinePoint_eq (ofAffinePoint σ x)
  exact ofAffinePoint_smul_eq_of_eq h.choose_spec.choose x t h.choose_spec.choose_spec

/-- The glued torus translations on algebraic complex points satisfy the group action laws. -/
noncomputable instance instMulActionComplexTorus :
    MulAction (ComplexTorus N) Φ.AlgebraicComplexPoint where
  one_smul p := by
    obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
    rw [smul_ofAffinePoint, one_smul]
  mul_smul s t p := by
    obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
    rw [smul_ofAffinePoint, smul_ofAffinePoint, smul_ofAffinePoint, mul_smul]

/-- Translation by a fixed torus element is continuous on algebraic complex points. -/
theorem continuous_const_smul (t : ComplexTorus N) :
    Continuous fun p : Φ.AlgebraicComplexPoint ↦ t • p := by
  refine continuous_iSup_dom.2 fun σ ↦ continuous_coinduced_dom.2 ?_
  let f : Φ.analyticAffineChart σ → Φ.analyticAffineChart σ :=
    fun x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) ↦ t • x
  have h : (fun p : Φ.AlgebraicComplexPoint ↦ t • p) ∘
      (fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x) =
      (fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x) ∘ f :=
    funext fun x ↦ smul_ofAffinePoint t σ x
  rw [h]
  have hc : Continuous f := by
    let g := Φ.analyticChartGenerators σ
    change Continuous[affinePointTopology g.2, affinePointTopology g.2]
      fun x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1) ↦ t • x
    exact AffineSemigroupComplexPoint.continuous_const_smul_affinePointTopology g.2
      (t.compAddMonoidHom (dualSemigroup Φ.lattice σ.1).subtype)
  exact (continuous_ofAffinePoint σ).comp hc

instance : ContinuousConstSMul (ComplexTorus N) Φ.AlgebraicComplexPoint :=
  ⟨continuous_const_smul⟩

/-- The distinguished complex point of a cone `σ` in the toric scheme: the image of the
distinguished point of the top face of `σ` in the affine chart of `σ`. -/
noncomputable def distinguishedPoint (σ : Φ.cones) : Φ.AlgebraicComplexPoint :=
  ofAffinePoint σ (TauCeti.Toric.distinguishedPoint Φ.lattice (⊤ : σ.1.Face))

/-- The distinguished point of a cone is the image of the distinguished point of its top face. -/
theorem distinguishedPoint_def (σ : Φ.cones) :
    distinguishedPoint σ =
      ofAffinePoint σ (TauCeti.Toric.distinguishedPoint Φ.lattice (⊤ : σ.1.Face)) :=
  (rfl)

/-- A face inclusion in the fan sends the distinguished point of the face to itself in the larger
chart. -/
theorem ofAffinePoint_distinguishedPoint {τ σ : Φ.cones} (h : τ ≤ σ) :
    ofAffinePoint σ (TauCeti.Toric.distinguishedPoint Φ.lattice (Φ.orbitFace h)) =
      distinguishedPoint τ := by
  have hd : faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 h)
      (TauCeti.Toric.distinguishedPoint Φ.lattice (⊤ : τ.1.Face)) =
        TauCeti.Toric.distinguishedPoint Φ.lattice (Φ.orbitFace h) :=
    faceAffinePointMap_distinguishedPoint Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 h)
      (by rw [Φ.coe_orbitFace h]; rfl)
  rw [distinguishedPoint_def, ← hd, ofAffinePoint_faceAffinePointMap]

/-- The canonical inclusion of the coordinate-free complex torus into the complex points of the
toric scheme of a nonempty fan, obtained by translating the distinguished point of the zero
cone. -/
noncomputable def torusι (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    Φ.AlgebraicComplexPoint :=
  t • distinguishedPoint ⟨⊥, Φ.bot_mem hΦ0.some.2⟩

theorem torusι_def (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    torusι hΦ0 t = t • distinguishedPoint ⟨⊥, Φ.bot_mem hΦ0.some.2⟩ :=
  (rfl)

/-- In every affine chart, the canonical torus inclusion is translation of the point `default`
where every monomial takes the value `1`. -/
theorem torusι_eq_ofAffinePoint (hΦ0 : Nonempty Φ.cones) (σ : Φ.cones) (t : ComplexTorus N) :
    torusι hΦ0 t = ofAffinePoint σ
      (t • (default : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))) := by
  let τ : Φ.cones := ⟨⊥, Φ.bot_mem hΦ0.some.2⟩
  have hle : τ ≤ σ := Subtype.coe_le_coe.1 bot_le
  have hface : Φ.orbitFace hle = (⊥ : σ.1.Face) := by
    apply le_antisymm
    · rw [← PointedCone.Face.toPointedCone_le_toPointedCone, Φ.coe_orbitFace]
      exact bot_le
    · exact bot_le
  rw [torusι_def, ← ofAffinePoint_distinguishedPoint hle, hface, distinguishedPoint_bot,
    smul_ofAffinePoint]

@[simp]
theorem torusι_one (hΦ0 : Nonempty Φ.cones) :
    torusι hΦ0 (1 : ComplexTorus N) = distinguishedPoint ⟨⊥, Φ.bot_mem hΦ0.some.2⟩ :=
  one_smul (ComplexTorus N) _

@[simp]
theorem torusι_mul (hΦ0 : Nonempty Φ.cones) (s t : ComplexTorus N) :
    torusι hΦ0 (s * t) = s • torusι hΦ0 t := by
  rw [torusι_def, torusι_def]
  exact @mul_smul (ComplexTorus N) Φ.AlgebraicComplexPoint inferInstance inferInstance s t
    (distinguishedPoint ⟨⊥, Φ.bot_mem hΦ0.some.2⟩)

/-! ### Global character functions on algebraic complex points -/

private theorem chartCharacter_eq_of_ofAffinePoint_eq
    (m : IntegralCharacter N) (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1)
    {σ τ : Φ.cones}
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
    (y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice τ.1))
    (h : ofAffinePoint σ x = ofAffinePoint τ y) :
    x (MonoidAlgebra.single (ofAdd ⟨m, hm σ⟩) 1) =
      y (MonoidAlgebra.single (ofAdd ⟨m, hm τ⟩) 1) := by
  obtain ⟨z, rfl, rfl⟩ := (ofAffinePoint_eq_ofAffinePoint_iff x y).1 h
  simp [faceAffinePointMap_def]
  rfl

variable (Φ) in
/-- An integral character `m` nonnegative on every cone of a fan defines a continuous function on
the complex points of the toric scheme, evaluating each affine chart point on the monomial of
`m`. -/
noncomputable def character (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1) :
    C(Φ.AlgebraicComplexPoint, ℂ) where
  toFun p :=
    let h := exists_ofAffinePoint_eq p
    h.choose_spec.choose (MonoidAlgebra.single (ofAdd ⟨m, hm h.choose⟩) 1)
  continuous_toFun := by
    refine continuous_iSup_dom.2 fun σ ↦ continuous_coinduced_dom.2 ?_
    have h : (fun p : Φ.AlgebraicComplexPoint ↦
        (exists_ofAffinePoint_eq p).choose_spec.choose
          (MonoidAlgebra.single (ofAdd ⟨m, hm (exists_ofAffinePoint_eq p).choose⟩) 1)) ∘
        (fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x) =
        fun x : Φ.analyticAffineChart σ ↦
          DFunLike.coe (F := AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) x
            (MonoidAlgebra.single (ofAdd ⟨m, hm σ⟩) 1) := by
      funext x
      exact chartCharacter_eq_of_ofAffinePoint_eq m hm _ _
        (exists_ofAffinePoint_eq (ofAffinePoint σ x)).choose_spec.choose_spec
    rw [h]
    let _ := affinePointTopology (Φ.analyticChartGenerators σ).2
    have hc := continuous_apply_single (Φ.analyticChartGenerators σ).2 ⟨m, hm σ⟩
    rwa [← Φ.analyticAffineChart_str_eq σ] at hc

/-- On every affine chart, the algebraic character function evaluates the point at the
corresponding monomial. -/
@[simp]
theorem character_ofAffinePoint (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1) (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    character Φ m hm (ofAffinePoint σ x) = x (MonoidAlgebra.single (ofAdd ⟨m, hm σ⟩) 1) :=
  chartCharacter_eq_of_ofAffinePoint_eq m hm _ _
    (exists_ofAffinePoint_eq (ofAffinePoint σ x)).choose_spec.choose_spec

/-- Character functions on algebraic complex points transform by their character under torus
translation. -/
@[simp]
theorem character_smul (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1)
    (t : ComplexTorus N) (p : Φ.AlgebraicComplexPoint) :
    character Φ m hm (t • p) = (t m : ℂ) * character Φ m hm p := by
  obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
  rw [smul_ofAffinePoint, character_ofAffinePoint, character_ofAffinePoint,
    AffineSemigroupComplexPoint.ambient_smul_apply_single]

/-- The zero character defines the constant function `1` on algebraic complex points. -/
@[simp]
theorem character_zero (p : Φ.AlgebraicComplexPoint) :
    character Φ 0 (fun σ ↦ (dualSemigroup Φ.lattice σ.1).zero_mem) p = 1 := by
  obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
  rw [character_ofAffinePoint]
  convert x.map_one using 1

/-- Addition of characters corresponds to multiplication of their functions on algebraic complex
points. -/
@[simp]
theorem character_add (m m' : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1)
    (hm' : ∀ σ : Φ.cones, m' ∈ dualSemigroup Φ.lattice σ.1)
    (p : Φ.AlgebraicComplexPoint) :
    character Φ (m + m') (fun σ ↦ (dualSemigroup Φ.lattice σ.1).add_mem (hm σ) (hm' σ)) p =
      character Φ m hm p * character Φ m' hm' p := by
  obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
  rw [character_ofAffinePoint, character_ofAffinePoint, character_ofAffinePoint]
  exact x.apply_single_add ⟨m, hm σ⟩ ⟨m', hm' σ⟩

/-- On the canonical dense-torus inclusion, the global character function restricts to evaluation
of the character. -/
@[simp]
theorem character_torusι (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1)
    (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    character Φ m hm (torusι hΦ0 t) = (t m : ℂ) := by
  rw [torusι_eq_ofAffinePoint hΦ0 hΦ0.some t, character_ofAffinePoint]
  simp [AffineSemigroupComplexPoint.ambient_smul_apply_single]

/-! ### Orbit strata and boundary components on algebraic complex points -/

variable (Φ) in
/-- The torus orbit of a cone `σ` in the complex points of the toric scheme: the image of the
stratum of the top face of `σ` in the affine chart of `σ`. -/
def coneOrbit (σ : Φ.cones) : Set Φ.AlgebraicComplexPoint :=
  ofAffinePoint σ '' affineConeOrbit Φ.lattice (⊤ : σ.1.Face)

theorem coneOrbit_def (σ : Φ.cones) :
    coneOrbit Φ σ = ofAffinePoint σ '' affineConeOrbit Φ.lattice (⊤ : σ.1.Face) :=
  (rfl)

/-- The distinguished point of a cone lies in its algebraic orbit. -/
theorem distinguishedPoint_mem_coneOrbit (σ : Φ.cones) :
    distinguishedPoint σ ∈ coneOrbit Φ σ :=
  ⟨TauCeti.Toric.distinguishedPoint Φ.lattice (⊤ : σ.1.Face),
    distinguishedPoint_mem_affineConeOrbit Φ.lattice _, rfl⟩

/-- The torus preserves the algebraic orbit of every cone. -/
theorem smul_mem_coneOrbit {σ : Φ.cones} (t : ComplexTorus N)
    {p : Φ.AlgebraicComplexPoint} (hp : p ∈ coneOrbit Φ σ) :
    t • p ∈ coneOrbit Φ σ := by
  rcases hp with ⟨x, hx, rfl⟩
  rw [smul_ofAffinePoint]
  exact ⟨t • x, (smul_mem_affineConeOrbit_iff Φ.lattice _ t).2 hx, rfl⟩

variable (Φ) in
/-- The boundary component indexed by a ray in the complex points of the toric scheme: the closure
of the torus orbit of that ray. -/
def boundaryComponent (ρ : Φ.Ray) : Set Φ.AlgebraicComplexPoint :=
  closure (coneOrbit Φ ρ.toCone)

theorem boundaryComponent_def (ρ : Φ.Ray) :
    boundaryComponent Φ ρ = closure (coneOrbit Φ ρ.toCone) :=
  (rfl)

theorem isClosed_boundaryComponent (ρ : Φ.Ray) :
    IsClosed (boundaryComponent Φ ρ) :=
  isClosed_closure

end AlgebraicComplexPoint

/-! ### Comparison with the analytic realization of a regular fan -/

variable {Φ} (hΦ : Φ.IsRegular)

open AlgebraicComplexPoint

/-- The algebraic–analytic comparison is equivariant for the coordinate-free complex torus. -/
@[simp]
theorem algebraicAnalyticEquiv_smul (t : ComplexTorus N) (p : Φ.AlgebraicComplexPoint) :
    algebraicAnalyticEquiv hΦ (t • p) = t • algebraicAnalyticEquiv hΦ p := by
  obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
  rw [smul_ofAffinePoint]
  erw [algebraicAnalyticEquiv_ofAffinePoint, algebraicAnalyticEquiv_ofAffinePoint,
    Φ.smul_analyticAffineChartι hΦ t σ x]
  rfl

/-- The inverse algebraic–analytic comparison is equivariant for the coordinate-free complex
torus. -/
@[simp]
theorem algebraicAnalyticEquiv_symm_smul (t : ComplexTorus N) (x : Φ.analyticRealization hΦ) :
    (algebraicAnalyticEquiv hΦ).symm (t • x) = t • (algebraicAnalyticEquiv hΦ).symm x := by
  apply (algebraicAnalyticEquiv hΦ).injective
  simp

/-- The algebraic–analytic homeomorphism is equivariant for the coordinate-free complex torus. -/
@[simp]
theorem algebraicAnalyticHomeomorph_smul (t : ComplexTorus N) (p : Φ.AlgebraicComplexPoint) :
    algebraicAnalyticHomeomorph hΦ (t • p) = t • algebraicAnalyticHomeomorph hΦ p := by
  simpa only [coe_algebraicAnalyticHomeomorph] using algebraicAnalyticEquiv_smul hΦ t p

include hΦ in
/-- For a regular fan, the complex torus acts jointly continuously on algebraic complex points. -/
theorem continuousSMul_algebraicComplexPoint :
    ContinuousSMul (ComplexTorus N) Φ.AlgebraicComplexPoint := by
  refine ⟨?_⟩
  have h : (fun q : ComplexTorus N × Φ.AlgebraicComplexPoint ↦ q.1 • q.2) =
      (algebraicAnalyticHomeomorph hΦ).symm ∘
        (fun q : ComplexTorus N × Φ.analyticRealization hΦ ↦ q.1 • q.2) ∘
          Prod.map id (algebraicAnalyticHomeomorph hΦ) := by
    funext ⟨t, p⟩
    simp
  rw [h]
  exact (algebraicAnalyticHomeomorph hΦ).symm.continuous.comp
    (continuous_smul.comp (continuous_id.prodMap (algebraicAnalyticHomeomorph hΦ).continuous))

/-- The algebraic–analytic comparison carries the distinguished point of every cone to its
analytic distinguished point. -/
@[simp]
theorem algebraicAnalyticEquiv_distinguishedPoint (σ : Φ.cones) :
    algebraicAnalyticEquiv hΦ (AlgebraicComplexPoint.distinguishedPoint σ) =
      Φ.analyticDistinguishedPoint hΦ σ := by
  rw [AlgebraicComplexPoint.distinguishedPoint_def, analyticDistinguishedPoint_def]
  exact algebraicAnalyticEquiv_ofAffinePoint hΦ σ _

/-- The inverse algebraic–analytic comparison carries the analytic distinguished point of every
cone to its algebraic distinguished point. -/
@[simp]
theorem algebraicAnalyticEquiv_symm_analyticDistinguishedPoint (σ : Φ.cones) :
    (algebraicAnalyticEquiv hΦ).symm (Φ.analyticDistinguishedPoint hΦ σ) =
      AlgebraicComplexPoint.distinguishedPoint σ := by
  apply (algebraicAnalyticEquiv hΦ).injective
  rw [Equiv.apply_symm_apply, algebraicAnalyticEquiv_distinguishedPoint]

/-- The algebraic–analytic comparison intertwines the canonical dense-torus inclusions. -/
@[simp]
theorem algebraicAnalyticEquiv_torusι (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    algebraicAnalyticEquiv hΦ (AlgebraicComplexPoint.torusι hΦ0 t) =
      Φ.analyticTorusι hΦ hΦ0 t := by
  rw [AlgebraicComplexPoint.torusι_def, algebraicAnalyticEquiv_smul,
    algebraicAnalyticEquiv_distinguishedPoint, analyticTorusι_def]

/-- The inverse algebraic–analytic comparison intertwines the canonical dense-torus inclusions. -/
@[simp]
theorem algebraicAnalyticEquiv_symm_analyticTorusι (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    (algebraicAnalyticEquiv hΦ).symm (Φ.analyticTorusι hΦ hΦ0 t) =
      AlgebraicComplexPoint.torusι hΦ0 t := by
  apply (algebraicAnalyticEquiv hΦ).injective
  simp

/-- The global character function on algebraic complex points agrees with `analyticCharacter`
through the algebraic–analytic comparison. -/
@[simp]
theorem analyticCharacter_algebraicAnalyticEquiv (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1) (p : Φ.AlgebraicComplexPoint) :
    Φ.analyticCharacter hΦ m hm (algebraicAnalyticEquiv hΦ p) =
      AlgebraicComplexPoint.character Φ m hm p := by
  obtain ⟨σ, x, rfl⟩ := exists_ofAffinePoint_eq p
  rw [character_ofAffinePoint]
  erw [algebraicAnalyticEquiv_ofAffinePoint, Φ.analyticCharacter_analyticAffineChartι hΦ m hm σ x]

/-- Pulling back `AlgebraicComplexPoint.character` along the inverse comparison recovers
`analyticCharacter`. -/
@[simp]
theorem character_algebraicAnalyticEquiv_symm (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1) (x : Φ.analyticRealization hΦ) :
    AlgebraicComplexPoint.character Φ m hm ((algebraicAnalyticEquiv hΦ).symm x) =
      Φ.analyticCharacter hΦ m hm x := by
  simpa using (analyticCharacter_algebraicAnalyticEquiv hΦ m hm
    ((algebraicAnalyticEquiv hΦ).symm x)).symm

/-- On a regular fan, the global character function on algebraic complex points is holomorphic. -/
theorem contMDiff_character_algebraicComplexPoint (m : IntegralCharacter N)
    (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1) (n : ℕ∞ω) :
    letI := algebraicComplexPointChartedSpace hΦ
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ℂ) n
      (AlgebraicComplexPoint.character Φ m hm) := by
  let _ := algebraicComplexPointChartedSpace hΦ
  let _ := Φ.analyticChartedSpace hΦ
  refine ((Φ.contMDiff_analyticCharacter hΦ m hm n).comp
    (algebraicAnalyticDiffeomorph hΦ n).contMDiff).congr fun p ↦ ?_
  simp

/-- For a regular fan, the complex torus acts holomorphically on algebraic complex points. -/
theorem contMDiffSMul_complexTorus_algebraicComplexPoint {ι : Type*} [Fintype ι]
    (e : IntegralCharacter N ≃+ (ι →₀ ℤ)) (n : ℕ∞ω) :
    let _ := complexTorusChartedSpace e
    letI := algebraicComplexPointChartedSpace hΦ
    ContMDiffSMul 𝓘(ℂ, ι → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) n (ComplexTorus N)
      Φ.AlgebraicComplexPoint := by
  let _ := complexTorusChartedSpace e
  let _ := algebraicComplexPointChartedSpace hΦ
  let _ := Φ.analyticChartedSpace hΦ
  have := Φ.contMDiffSMul_complexTorus_analyticRealization hΦ e n
  refine ⟨?_⟩
  have h : (fun q : ComplexTorus N × Φ.AlgebraicComplexPoint ↦ q.1 • q.2) =
      (algebraicAnalyticDiffeomorph hΦ n).symm ∘
        (fun q : ComplexTorus N × Φ.analyticRealization hΦ ↦ q.1 • q.2) ∘
          Prod.map id (algebraicAnalyticDiffeomorph hΦ n) := by
    funext ⟨t, p⟩
    simp
  rw [h]
  exact (algebraicAnalyticDiffeomorph hΦ n).symm.contMDiff.comp
    (contMDiff_smul.comp (contMDiff_id.prodMap (algebraicAnalyticDiffeomorph hΦ n).contMDiff))

/-- The algebraic–analytic comparison carries the algebraic orbit of each cone onto its analytic
cone orbit. -/
@[simp]
theorem image_algebraicAnalyticEquiv_coneOrbit (σ : Φ.cones) :
    algebraicAnalyticEquiv hΦ '' AlgebraicComplexPoint.coneOrbit Φ σ =
      Φ.analyticConeOrbit hΦ σ := by
  rw [AlgebraicComplexPoint.coneOrbit_def, analyticConeOrbit_def, ← Set.image_comp]
  refine congrFun (congrArg Set.image (funext fun x ↦ ?_)) _
  exact algebraicAnalyticEquiv_ofAffinePoint hΦ σ x

/-- The preimage of the analytic orbit of a cone under the comparison is its algebraic orbit. -/
@[simp]
theorem preimage_algebraicAnalyticEquiv_analyticConeOrbit (σ : Φ.cones) :
    algebraicAnalyticEquiv hΦ ⁻¹' Φ.analyticConeOrbit hΦ σ =
      AlgebraicComplexPoint.coneOrbit Φ σ := by
  rw [← image_algebraicAnalyticEquiv_coneOrbit hΦ σ,
    (algebraicAnalyticEquiv hΦ).preimage_image]

include hΦ in
/-- For a regular fan, the algebraic orbit of a cone `σ` is the torus orbit of its distinguished
point. -/
theorem coneOrbit_eq_orbit (σ : Φ.cones) :
    AlgebraicComplexPoint.coneOrbit Φ σ =
      MulAction.orbit (ComplexTorus N) (AlgebraicComplexPoint.distinguishedPoint σ) := by
  ext p
  rw [← preimage_algebraicAnalyticEquiv_analyticConeOrbit hΦ σ, Set.mem_preimage,
    analyticConeOrbit_eq_orbit]
  refine ⟨fun ⟨t, ht⟩ ↦ ⟨t, ?_⟩, fun ⟨t, ht⟩ ↦ ⟨t, ?_⟩⟩
  · apply (algebraicAnalyticEquiv hΦ).injective
    rwa [algebraicAnalyticEquiv_smul, algebraicAnalyticEquiv_distinguishedPoint]
  · rw [← ht, algebraicAnalyticEquiv_smul, algebraicAnalyticEquiv_distinguishedPoint]

/-- The algebraic–analytic comparison carries the algebraic boundary component of each ray onto
its analytic boundary component. -/
@[simp]
theorem image_algebraicAnalyticEquiv_boundaryComponent (ρ : Φ.Ray) :
    algebraicAnalyticEquiv hΦ '' AlgebraicComplexPoint.boundaryComponent Φ ρ =
      Φ.analyticBoundaryComponent hΦ ρ := by
  rw [AlgebraicComplexPoint.boundaryComponent_def, analyticBoundaryComponent_def,
    ← coe_algebraicAnalyticHomeomorph, (algebraicAnalyticHomeomorph hΦ).image_closure,
    coe_algebraicAnalyticHomeomorph, image_algebraicAnalyticEquiv_coneOrbit]

/-- The preimage of the analytic boundary component of a ray under the comparison is its
algebraic boundary component. -/
@[simp]
theorem preimage_algebraicAnalyticEquiv_analyticBoundaryComponent (ρ : Φ.Ray) :
    algebraicAnalyticEquiv hΦ ⁻¹' Φ.analyticBoundaryComponent hΦ ρ =
      AlgebraicComplexPoint.boundaryComponent Φ ρ := by
  rw [← image_algebraicAnalyticEquiv_boundaryComponent hΦ ρ,
    (algebraicAnalyticEquiv hΦ).preimage_image]

include hΦ in
/-- For a nonempty regular fan, the space of algebraic complex points is compact if and only if
the fan is complete. -/
theorem compactSpace_algebraicComplexPoint_iff_isComplete (hΦ0 : Nonempty Φ.cones) :
    CompactSpace Φ.AlgebraicComplexPoint ↔ Φ.IsComplete := by
  have hcomp : CompactSpace Φ.AlgebraicComplexPoint ↔ CompactSpace (Φ.analyticRealization hΦ) :=
    ⟨fun _ ↦ (algebraicAnalyticHomeomorph hΦ).compactSpace,
      fun _ ↦ (algebraicAnalyticHomeomorph hΦ).symm.compactSpace⟩
  exact hcomp.trans (Φ.compactSpace_analyticRealization_iff_isComplete hΦ hΦ0)

end Fan

namespace FanHom

variable {N' V' : Type} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'} (f : FanHom Φ Ψ)

/-- The map on algebraic complex points induced by a fan morphism is equivariant for the torus
homomorphism induced by its lattice map. -/
@[simp]
theorem algebraicComplexPointMap_smul (t : ComplexTorus N) (p : Φ.AlgebraicComplexPoint) :
    f.algebraicComplexPointMap (t • p) =
      complexTorusMap f.latticeMap t • f.algebraicComplexPointMap p := by
  obtain ⟨σ, x, rfl⟩ := Fan.AlgebraicComplexPoint.exists_ofAffinePoint_eq p
  rw [Fan.AlgebraicComplexPoint.smul_ofAffinePoint, algebraicComplexPointMap_ofAffinePoint,
    algebraicComplexPointMap_ofAffinePoint]
  erw [Fan.AlgebraicComplexPoint.smul_ofAffinePoint, f.analyticChartMap_smul]
  rfl

/-- On the canonical dense-torus inclusion, the map on algebraic complex points is the torus
homomorphism induced by the lattice map. -/
@[simp]
theorem algebraicComplexPointMap_torusι (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    f.algebraicComplexPointMap (Fan.AlgebraicComplexPoint.torusι hΦ0 t) =
      Fan.AlgebraicComplexPoint.torusι
        ⟨⟨f.leastCone hΦ0.some.2, f.leastCone_mem hΦ0.some.2⟩⟩
        (complexTorusMap f.latticeMap t) := by
  let σ := hΦ0.some
  let τ : Ψ.cones := ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩
  rw [Fan.AlgebraicComplexPoint.torusι_eq_ofAffinePoint hΦ0 σ,
    Fan.AlgebraicComplexPoint.torusι_eq_ofAffinePoint ⟨τ⟩ τ,
    algebraicComplexPointMap_ofAffinePoint]
  erw [f.analyticChartMap_smul]
  congr 2
  erw [analyticChartMap_apply, AffineSemigroupComplexPoint.comap_default]

/-- Pullback of a global character function on algebraic complex points along a fan morphism
precomposes the character with the integral lattice map. -/
@[simp]
theorem character_algebraicComplexPointMap (m : IntegralCharacter N')
    (hm : ∀ τ : Ψ.cones, m ∈ dualSemigroup Ψ.lattice τ.1) (p : Φ.AlgebraicComplexPoint) :
    Fan.AlgebraicComplexPoint.character Ψ m hm (f.algebraicComplexPointMap p) =
      Fan.AlgebraicComplexPoint.character Φ (m.comp f.latticeMap)
        (fun σ ↦ by
          rw [mem_dualSemigroup, Φ.lattice.realCharacter_comp Ψ.lattice
            f.latticeMap f.realMap f.map_lattice]
          intro v hv
          exact (mem_dualSemigroup Ψ.lattice m).1
            (hm ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) (f.mapsTo_leastCone σ.2 hv)) p := by
  obtain ⟨σ, x, rfl⟩ := Fan.AlgebraicComplexPoint.exists_ofAffinePoint_eq p
  rw [algebraicComplexPointMap_ofAffinePoint, Fan.AlgebraicComplexPoint.character_ofAffinePoint]
  erw [Fan.AlgebraicComplexPoint.character_ofAffinePoint, analyticChartMap_apply,
    AffineSemigroupComplexPoint.comap_apply_single]
  congr 2
  apply Subtype.ext
  ext n
  exact dualSemigroupMap_apply Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
    (f.mapsTo_leastCone σ.2) _ n

end FanHom

end TauCeti.Toric
