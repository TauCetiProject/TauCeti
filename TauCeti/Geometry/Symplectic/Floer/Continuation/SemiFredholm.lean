/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Continuation
public import TauCeti.Geometry.Symplectic.Floer.Continuation.AlmostComplex
public import TauCeti.Geometry.Symplectic.Floer.Continuation.Path
public import TauCeti.Geometry.Symplectic.Floer.SemiFredholm

/-!
# The semi-Fredholm estimate of the linearized Floer operator along a continuation cylinder

A Floer continuation cylinder from `H₋` to `H₊` solves the Floer equation for the
`s`-dependent Hamiltonian `TauCeti.Floer.continuationHomotopy H₋ H₊`, which is `H₋` for `s ≤ 0`
and `H₊` for `s ≥ 1`, with the almost complex structures
`TauCeti.Floer.continuationAlmostComplex h₀ J₋ J₊`, which are `J₋` for `s ≤ 0` and `J₊` for
`s ≥ 1`. These data are cylindrical outside `[0, 1] × S¹`, with different Hamiltonians and
almost complex structures at the two ends
(`TauCeti.Floer.isCylindricalNearEnds_continuationHomotopy`), so the semi-Fredholm estimate for
data that are cylindrical near the ends,
`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical`
in `TauCeti.Geometry.Symplectic.Floer.SemiFredholm`, applies to them. Likewise the path
(`TauCeti.Floer.pathAlmostComplex`, `TauCeti.Floer.pathHamiltonian`) between two sets of data that
are cylindrical near the ends with the same end Hamiltonians stays cylindrical near the ends
(`TauCeti.Floer.isCylindricalNearEnds_path`). This file records the
resulting estimate for the linearized operator `D_u` along a map `u` of the cylinder asymptotic to
a nondegenerate one-periodic orbit `x₋` of `H₋` at `-∞` and to a nondegenerate one-periodic orbit
`x₊` of `H₊` at `+∞`: there are `C ≥ 0` and `T` such that

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

for every `C²` section `ξ` of period one in `t` vanishing outside a strip `(a, b) × ℝ`
(`exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add`, in
the namespace `TauCeti.SymplecticForm`).
This is the a priori estimate behind finite dimensional kernel and closed range of the linearized
operator of continuation cylinders, whose counts define continuation maps. The Sobolev completion
and the Fredholm property itself are not treated here.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lectures 2 and 3, on the Fredholm property of the linearized operator and
  on continuation maps.
-/

public section

open Set Filter
open scoped NNReal Manifold

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The continuation data from `(J₋, H₋)` to `(J₊, H₊)`, for `C¹` families `J±_t(y)` of `ω`-tame
almost complex structures and jointly `C²` Hamiltonians `H±`, are cylindrical near the ends with
radius `1` and end data `(J₋, H₋)` and `(J₊, H₊)`, along any map `u`. -/
theorem isCylindricalNearEnds_continuationHomotopy {ω : SymplecticForm V}
    {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jm Jp : ℝ → V → AlmostComplexStructure V} {hJmt : ∀ t x, ω.Tames (Jm t x)}
    {hJpt : ∀ t x, ω.Tames (Jp t x)}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Hm Hp : ℝ → V → ℝ} (hHm : ContDiff ℝ 2 (Function.uncurry Hm))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) (u : ℝ × ℝ → V) :
    IsCylindricalNearEnds (continuationAlmostComplex h₀ Jm Jp hJmt hJpt) (fun _ _ ↦ 0)
      (continuationHomotopy Hm Hp) Jm Jp Hm Hp 1 u where
  almostComplex_eq_of_le_neg _ hz :=
    funext (continuationAlmostComplex_of_nonpos h₀ (hz.trans (by norm_num)))
  almostComplex_eq_of_le _ hz := funext (continuationAlmostComplex_of_one_le h₀ hz)
  hamiltonianS_eq_zero _ _ := rfl
  hamiltonianT_eq_of_le_neg _ hz := funext (continuationHomotopy_of_nonpos (hz.trans (by norm_num)))
  hamiltonianT_eq_of_le _ hz := funext (continuationHomotopy_of_one_le hz)
  contDiffAt_almostComplex _ := (contDiff_continuationAlmostComplex h₀ hJm hJp).contDiffAt
  contDiffAt_hamiltonianS _ := contDiffAt_const
  contDiffAt_hamiltonianT _ := (contDiff_uncurry_continuationHomotopy hHm hHp).contDiffAt

/-- Let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be two sets of Floer data on a domain `Z` whose
pullbacks along a `C²` map `f` from the cylinder to `Z` are cylindrical near the ends with the same
end Hamiltonians, with radii `R` and `R'`. Then the pullbacks along `f` of the path of data between
them are all cylindrical near the ends with the radius `max R R'` and the same end Hamiltonians. At
the parameter `μ` the almost complex structures of the ends are those of the path at
`f (∓ max R R', t)`. With `f` the identity this joins two sets of data on the cylinder; with
`f = (ν, ·)` it joins the data at the parameter `ν` of two families of data. -/
theorem isCylindricalNearEnds_path {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    (h₀ : ω.Compatible J₀) {J J' : Z → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : Z → V → ℝ}
    {Hm Hp : ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u : ℝ × ℝ → V} {f : ℝ × ℝ → Z} (hf : ContDiff ℝ 2 f)
    (hcyl : IsCylindricalNearEnds (fun w ↦ J (f w)) (fun w ↦ Ks (f w)) (fun w ↦ Kt (f w))
      Jm Jp Hm Hp R u)
    (hcyl' : IsCylindricalNearEnds (fun w ↦ J' (f w)) (fun w ↦ Ks' (f w))
      (fun w ↦ Kt' (f w)) Jm' Jp' Hm Hp R' u)
    (hJt : ∀ z y, ω.Tames (J z y)) (hJ't : ∀ z y, ω.Tames (J' z y))
    (hJ : ContDiff ℝ 1 fun p : Z × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ' : ContDiff ℝ 1 fun p : Z × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (Function.uncurry Ks)) (hKs' : ContDiff ℝ 2 (Function.uncurry Ks'))
    (hKt : ContDiff ℝ 2 (Function.uncurry Kt)) (hKt' : ContDiff ℝ 2 (Function.uncurry Kt'))
    (μ : ℝ) :
    IsCylindricalNearEnds (fun w ↦ pathAlmostComplex h₀ hJt hJ't (μ, f w))
      (fun w ↦ pathHamiltonian Ks Ks' (μ, f w))
      (fun w ↦ pathHamiltonian Kt Kt' (μ, f w))
      (fun t ↦ pathAlmostComplex h₀ hJt hJ't (μ, f (-max R R', t)))
      (fun t ↦ pathAlmostComplex h₀ hJt hJ't (μ, f (max R R', t))) Hm Hp (max R R') u := by
  have h₁ := hcyl.mono (le_max_left R R')
  have h₂ := hcyl'.mono (le_max_right R R')
  -- Where both Hamiltonians equal the same end Hamiltonian, so does every point of the path.
  have hKeq {K K' : Z → V → ℝ} {z : Z} (e : V → ℝ) (he : K z = e) (he' : K' z = e) :
      pathHamiltonian K K' (μ, z) = e :=
    (pathHamiltonian_of_eq μ (he.trans he'.symm)).trans he
  -- The pullback along `f` at the parameter `μ` is a `C²` map into the domain of the path.
  have hg : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦ ((μ, f p.1), p.2) :=
    (contDiff_const.prodMk (hf.comp contDiff_fst)).prodMk contDiff_snd
  exact
    { almostComplex_eq_of_le_neg := fun z hz ↦ pathAlmostComplex_congr h₀ μ
        ((h₁.almostComplex_eq_of_le_neg z hz).trans
          (h₁.almostComplex_eq_of_le_neg (_, z.2) le_rfl).symm)
        ((h₂.almostComplex_eq_of_le_neg z hz).trans
          (h₂.almostComplex_eq_of_le_neg (_, z.2) le_rfl).symm)
      almostComplex_eq_of_le := fun z hz ↦ pathAlmostComplex_congr h₀ μ
        ((h₁.almostComplex_eq_of_le z hz).trans (h₁.almostComplex_eq_of_le (_, z.2) le_rfl).symm)
        ((h₂.almostComplex_eq_of_le z hz).trans (h₂.almostComplex_eq_of_le (_, z.2) le_rfl).symm)
      hamiltonianS_eq_zero := fun z hz ↦ hKeq _ (h₁.hamiltonianS_eq_zero z hz)
        (h₂.hamiltonianS_eq_zero z hz)
      hamiltonianT_eq_of_le_neg := fun z hz ↦ hKeq _ (h₁.hamiltonianT_eq_of_le_neg z hz)
        (h₂.hamiltonianT_eq_of_le_neg z hz)
      hamiltonianT_eq_of_le := fun z hz ↦ hKeq _ (h₁.hamiltonianT_eq_of_le z hz)
        (h₂.hamiltonianT_eq_of_le z hz)
      contDiffAt_almostComplex := fun _ ↦
        ((contDiff_pathAlmostComplex h₀ hJt hJ't hJ hJ').comp
          (hg.of_le one_le_two)).contDiffAt
      contDiffAt_hamiltonianS := fun _ ↦
        ((contDiff_pathHamiltonian hKs hKs').comp hg).contDiffAt
      contDiffAt_hamiltonianT := fun _ ↦
        ((contDiff_pathHamiltonian hKt hKt').comp hg).contDiffAt }

end TauCeti.Floer

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

open Floer in
/-- **The semi-Fredholm estimate along a continuation cylinder.** Let `H₋`, `H₊` be jointly `C²`
Hamiltonians with globally Lipschitz suspended vector fields, and `J₋_t(y)`, `J₊_t(y)` be `C¹`
families of `ω`-tame almost complex structures. Let `u : ℝ × ℝ → V` be a `C¹` map along which the
continuation homotopy of almost complex structures from `J₋` to `J₊` is `ω`-compatible, whose
loops converge uniformly at `-∞` to an orbit `x₋` of `H₋` and at `+∞` to an orbit `x₊` of `H₊`,
starting at nondegenerate fixed points of the time-one maps and along which `J₋`, respectively
`J₊`, is compatible, while the slice defects `∂t u - X_{H±_t}(u)` tend uniformly to zero there.
Then there are `C ≥ 0` and `T` such that every `C²` map `ξ` of period one in `t` vanishing for
`s ∉ (a, b)` satisfies

`∫ (‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²) ≤ C (∫ ‖D_u ξ‖² + ∫_{[-T, T] × [0, 1]} ‖ξ‖²)`

over `[a, b] × [0, 1]`, for the linearized Floer operator `D_u` of the continuation datum
`K = H_{(s, t)} dt`, `H = continuationHomotopy H₋ H₊`. -/
theorem exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_continuationHomotopy_add
    (ω : SymplecticForm V) {J₀ : AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    {Jm Jp : ℝ → V → AlmostComplexStructure V} {hJmt : ∀ t x, ω.Tames (Jm t x)}
    {hJpt : ∀ t x, ω.Tames (Jp t x)}
    (hJm : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jm p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJp : ContDiff ℝ 1 fun p : ℝ × V ↦ (Jp p.1 p.2).toLinearMap.toContinuousLinearMap)
    {Hm Hp : ℝ → V → ℝ} {Km Kp : ℝ≥0}
    (hXm : LipschitzWith Km (ω.timeDependentHamiltonianSuspension Hm))
    (hHm : ContDiff ℝ 2 (Function.uncurry Hm))
    (hXp : LipschitzWith Kp (ω.timeDependentHamiltonianSuspension Hp))
    (hHp : ContDiff ℝ 2 (Function.uncurry Hp)) {xm xp : ℝ → V}
    (hxm : ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm t) (xm t)) t)
    (hndm : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hm hXm 0 1) (xm 0))
    (hJxm : ∀ t, ω.Compatible (Jm t (xm t)))
    (hxp : ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp t) (xp t)) t)
    (hndp : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow Hp hXp 0 1) (xp 0))
    (hJxp : ∀ t, ω.Compatible (Jp t (xp t))) {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u)
    (hJu : ∀ z, ω.Compatible (continuationAlmostComplex h₀ Jm Jp hJmt hJpt z (u z)))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp t)) u (s, t)) 0 atTop
        (Icc 0 1)) :
    ∃ C, 0 ≤ C ∧ ∃ T, ∀ ⦃ξ : ℝ × ℝ → V⦄, ContDiff ℝ 2 ξ → (∀ s t, ξ (s, t + 1) = ξ (s, t)) →
      ∀ ⦃a b : ℝ⦄, a ≤ b → (∀ s t, s ∉ Ioo a b → ξ (s, t) = 0) →
        ∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, (‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 +
            ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2) ≤
          C * ((∫ z in Icc a b ×ˢ Icc (0 : ℝ) 1, ‖ω.floerLinearization
            (fun w y ↦ (continuationAlmostComplex h₀ Jm Jp hJmt hJpt w y).toLinearMap
              |>.toContinuousLinearMap)
            (fun _ _ ↦ 0) (continuationHomotopy Hm Hp) u ξ z‖ ^ 2) +
            ∫ z in Icc (-T) T ×ˢ Icc (0 : ℝ) 1, ‖ξ z‖ ^ 2) :=
  ω.exists_forall_setIntegral_le_mul_setIntegral_floerLinearization_add_of_cylindrical
    (isCylindricalNearEnds_continuationHomotopy h₀ hJm hJp hHm hHp u) hu hJu hXm hHm hxm hndm hJm
    hJxm huxm hδm hXp hHp hxp hndp hJp hJxp huxp hδp

end TauCeti.SymplecticForm
