/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.DenseTorus
public import TauCeti.Geometry.Toric.Analytic.Fan.Map.Basic

/-!
# Holomorphic characters on a toric fan realization

An integral character nonnegative on every cone of a regular fan defines a holomorphic
function on its analytic realization. The affine monomial functions agree under face
localization, so they descend through the gluing. Their products correspond to sums of
characters, and torus translation multiplies them by the corresponding character value.
For a nonempty fan, these functions are the unique continuous extensions of the characters
on its dense torus. Pullback along a toric map precomposes the character with the
map of integral lattices.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3 and 3.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open Multiplicative Set Topology
open scoped ContDiff Manifold

namespace TauCeti.Toric.Fan

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i) (hΦ : Φ.IsRegular)
  (m : IntegralCharacter N) (hm : ∀ σ : Φ.cones, m ∈ dualSemigroup Φ.lattice σ.1)

private noncomputable def chartCharacter (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) : ℂ :=
  x (MonoidAlgebra.single (ofAdd ⟨m, hm σ⟩) 1)

private theorem chartCharacter_eq_of_eq {σ τ : Φ.cones}
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
    (y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice τ.1))
    (h : Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ τ y) :
    Φ.chartCharacter m hm σ x = Φ.chartCharacter m hm τ y := by
  obtain ⟨z, rfl, rfl⟩ := (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ x y).mp h
  simp only [chartCharacter, analyticOverlapLeft_def, analyticOverlapRight_def,
    analyticAffineChartDiagram_map_apply]
  -- Diagram maps are stated on bundled charts, while the pullback formula uses affine points.
  erw [AffineSemigroupComplexPoint.comap_apply_single,
    AffineSemigroupComplexPoint.comap_apply_single]
  rfl

private noncomputable def characterFun (p : Φ.analyticRealization hΦ) : ℂ :=
  let h := Φ.exists_analyticAffineChartι_apply_eq hΦ p
  Φ.chartCharacter m hm h.choose h.choose_spec.choose

private theorem characterFun_analyticAffineChartι (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    Φ.characterFun hΦ m hm (Φ.analyticAffineChartι hΦ σ x) =
      Φ.chartCharacter m hm σ x := by
  let h := Φ.exists_analyticAffineChartι_apply_eq hΦ (Φ.analyticAffineChartι hΦ σ x)
  exact Φ.chartCharacter_eq_of_eq hΦ m hm _ _ h.choose_spec.choose_spec

/-- The holomorphic monomial function of an integral character nonnegative on every cone.
Its restriction to each affine chart is evaluation on the corresponding monomial. -/
noncomputable def analyticCharacter : C(Φ.analyticRealization hΦ, ℂ) where
  toFun := Φ.characterFun hΦ m hm
  continuous_toFun := by
    apply continuous_def.2
    intro s hs
    rw [Φ.isOpen_iff_forall_preimage_analyticAffineChartι hΦ]
    intro σ
    have heq : Φ.characterFun hΦ m hm ∘ Φ.analyticAffineChartι hΦ σ =
        Φ.chartCharacter m hm σ := funext (Φ.characterFun_analyticAffineChartι hΦ m hm σ)
    rw [← preimage_comp, heq]
    let _ := affinePointTopology (Φ.analyticChartGenerators σ).2
    have hc := continuous_apply_single (Φ.analyticChartGenerators σ).2 ⟨m, hm σ⟩
    rw [← Φ.analyticAffineChart_str_eq σ] at hc
    exact hc.isOpen_preimage s hs

/-- The character function is the expected monomial on every affine chart. -/
@[simp]
theorem analyticCharacter_analyticAffineChartι (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj σ) :
    Φ.analyticCharacter hΦ m hm (Φ.analyticAffineChartι hΦ σ x) =
      DFunLike.coe (F := AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) x
        (MonoidAlgebra.single (ofAdd ⟨m, hm σ⟩) 1) :=
  Φ.characterFun_analyticAffineChartι hΦ m hm σ x

/-- Character functions transform by their character under torus translation. -/
@[simp]
theorem analyticCharacter_smul (t : ComplexTorus N) (x : Φ.analyticRealization hΦ) :
    Φ.analyticCharacter hΦ m hm (t • x) =
      (t m : ℂ) * Φ.analyticCharacter hΦ m hm x := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  rw [smul_analyticAffineChartι]
  -- The representatives have the bundled chart carrier, so use full transparency to
  -- match the monomial equation on the affine complex-point carrier.
  erw [analyticCharacter_analyticAffineChartι, analyticCharacter_analyticAffineChartι]
  exact AffineSemigroupComplexPoint.ambient_smul_apply_single t y ⟨m, hm σ⟩

/-- The zero character defines the constant function one. -/
@[simp]
theorem analyticCharacter_zero (x : Φ.analyticRealization hΦ) :
    Φ.analyticCharacter hΦ 0 (fun σ ↦ (dualSemigroup Φ.lattice σ.1).zero_mem) x = 1 := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  -- Identify the bundled chart carrier with its affine complex-point carrier.
  erw [analyticCharacter_analyticAffineChartι]
  -- The subtype representing the zero character is the zero of the dual semigroup.
  convert y.map_one using 1

/-- Addition of characters corresponds to multiplication of their holomorphic functions. -/
@[simp]
theorem analyticCharacter_add (m' : IntegralCharacter N)
    (hm' : ∀ σ : Φ.cones, m' ∈ dualSemigroup Φ.lattice σ.1)
    (x : Φ.analyticRealization hΦ) :
    Φ.analyticCharacter hΦ (m + m')
        (fun σ ↦ (dualSemigroup Φ.lattice σ.1).add_mem (hm σ) (hm' σ)) x =
      Φ.analyticCharacter hΦ m hm x * Φ.analyticCharacter hΦ m' hm' x := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  -- Identify the bundled chart carrier with its affine complex-point carrier.
  erw [analyticCharacter_analyticAffineChartι, analyticCharacter_analyticAffineChartι,
    analyticCharacter_analyticAffineChartι]
  exact y.apply_single_add ⟨m, hm σ⟩ ⟨m', hm' σ⟩

/-- The glued character function is holomorphic for the canonical complex structure. -/
theorem contMDiff_analyticCharacter (n : ℕ∞ω) :
    let _ := Φ.analyticChartedSpace hΦ
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, ℂ) n
      (Φ.analyticCharacter hΦ m hm) := by
  intro _ p
  obtain ⟨σ, x, hx⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ p
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay σ.1) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay σ.1)
  let g := (Φ.analyticChartGenerators σ).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace Φ.lattice hσ.toIsToricCone hB κ g
  let P := Φ.analyticAffineChartPartialDiffeomorph hΦ σ hB κ g n
  have hp : p ∈ P.target := by
    rw [analyticAffineChartPartialDiffeomorph_target]
    exact ⟨x, hx⟩
  have hmono := contMDiff_apply_single Φ.lattice hσ.toIsToricCone hB κ g ⟨m, hm σ⟩ n
  have hloc := hmono.comp_contMDiffOn P.symm.contMDiffOn
  refine (hloc.contMDiffAt (P.open_target.mem_nhds hp)).congr_of_eventuallyEq ?_
  filter_upwards [P.open_target.mem_nhds hp] with y hy
  have heq := P.right_inv hy
  rw [analyticAffineChartPartialDiffeomorph_apply] at heq
  exact (congrArg (Φ.analyticCharacter hΦ m hm) heq.symm).trans
    (Φ.analyticCharacter_analyticAffineChartι hΦ m hm σ (P.symm y))

/-- The global function restricts to the original character on the dense torus. -/
@[simp]
theorem analyticCharacter_analyticTorusι (hΦ0 : Nonempty Φ.cones) (t : ComplexTorus N) :
    Φ.analyticCharacter hΦ m hm (Φ.analyticTorusι hΦ hΦ0 t) = (t m : ℂ) := by
  rw [Φ.analyticTorusι_eq_analyticAffineChartι hΦ hΦ0 hΦ0.some t]
  -- The torus formula uses the affine-point carrier of the chart representative.
  erw [analyticCharacter_analyticAffineChartι]
  simp [AffineSemigroupComplexPoint.ambient_smul_apply_single]

/-- A continuous extension of a character from the dense torus is the glued character function.
The nonempty hypothesis supplies the dense torus; the construction itself also allows empty fans. -/
theorem eq_analyticCharacter_iff (hΦ0 : Nonempty Φ.cones)
    (f : C(Φ.analyticRealization hΦ, ℂ)) :
    f = Φ.analyticCharacter hΦ m hm ↔
      ∀ t, f (Φ.analyticTorusι hΦ hΦ0 t) = (t m : ℂ) := by
  constructor
  · rintro rfl
    exact Φ.analyticCharacter_analyticTorusι hΦ m hm hΦ0
  · intro h
    have hd : DenseRange (Φ.analyticTorusι hΦ hΦ0) := by
      rw [DenseRange, Φ.range_analyticTorusι hΦ hΦ0]
      exact Φ.dense_analyticDenseTorus hΦ hΦ0
    apply ContinuousMap.ext
    exact congrFun (hd.equalizer f.continuous (Φ.analyticCharacter hΦ m hm).continuous
      (funext fun t ↦ (h t).trans (Φ.analyticCharacter_analyticTorusι hΦ m hm hΦ0 t).symm))

end TauCeti.Toric.Fan

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}

/-- Pullback of a global holomorphic character along a toric map is the character obtained
by precomposition with its integral lattice map. Nonnegativity on the source follows from
nonnegativity on the target and the fan-morphism condition. -/
@[simp]
theorem analyticCharacter_analyticMap (f : FanHom Φ Ψ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
    (m : IntegralCharacter N') (hm : ∀ τ : Ψ.cones, m ∈ dualSemigroup Ψ.lattice τ.1)
    (x : Φ.analyticRealization hΦ) :
    Ψ.analyticCharacter hΨ m hm (f.analyticMap hΦ hΨ x) =
      Φ.analyticCharacter hΦ (m.comp f.latticeMap)
        (fun σ ↦ by
          rw [mem_dualSemigroup, Φ.lattice.realCharacter_comp Ψ.lattice
            f.latticeMap f.realMap f.map_lattice]
          intro v hv
          exact (mem_dualSemigroup Ψ.lattice m).1
            (hm ⟨f.leastCone σ.2, f.leastCone_mem σ.2⟩) (f.mapsTo_leastCone σ.2 hv)) x := by
  obtain ⟨σ, y, rfl⟩ := Φ.exists_analyticAffineChartι_apply_eq hΦ x
  rw [analyticMap_analyticAffineChartι, Fan.analyticCharacter_analyticAffineChartι,
    Fan.analyticCharacter_analyticAffineChartι]
  -- The diagram map and its pullback formula use definitionally equal chart carriers.
  erw [analyticChartMap_apply, AffineSemigroupComplexPoint.comap_apply_single]
  congr 2
  apply Subtype.ext
  ext n
  exact dualSemigroupMap_apply Φ.lattice Ψ.lattice f.latticeMap f.realMap f.map_lattice
    (f.mapsTo_leastCone σ.2) _ n

end TauCeti.Toric.FanHom
