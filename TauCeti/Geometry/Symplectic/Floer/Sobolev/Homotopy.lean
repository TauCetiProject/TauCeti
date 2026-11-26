/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm
import TauCeti.Geometry.Symplectic.Floer.Continuation
import TauCeti.Geometry.Symplectic.Floer.Continuation.SemiFredholm

/-!
# Homotopy invariance of the index of the linearized Floer operator

Let `D_u : W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` be the Sobolev realization
(`TauCeti.SymplecticForm.floerSobolevOperator`) of the linearized Floer operator along a map
`u : ℝ × ℝ → V` into a finite-dimensional symplectic inner product space, for Floer data
`(J, K_s, K_t)` that are `C¹` (with `C²` Hamiltonians), compatible with `ω`, and cylindrical near
the ends (`TauCeti.Floer.IsCylindricalNearEnds`) with end Hamiltonians `H₋` and `H₊`, along which
`u` is asymptotic to nondegenerate one-periodic orbits `x₋` and `x₊`.
`TauCeti.Geometry.Symplectic.Floer.Sobolev.Fredholm` shows that the Fredholm property and the index
of `D_u` depend only on `H±` and `x±`. This file shows that they depend on the end Hamiltonians
only through their homotopy class: if `H±_μ`, `0 ≤ μ ≤ 1`, are homotopies of end Hamiltonians,
jointly `C²` in the parameter, the time and the point, along which `x±` stay nondegenerate
one-periodic orbits, then the operator of data with ends `H±_0` along `u` is Fredholm exactly
when the operator of data with ends `H±_1` along a second map `u'` asymptotic to the same orbits
is (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_homotopy`), and then the two
have the same index (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_of_homotopy`). The
almost complex structures, the Hamiltonians away from the ends and the maps are arbitrary on
both sides. This is the homotopy axiom of the index: together with its catenation under gluing
and its normalization at the constant orbits of a small Hamiltonian, it is how the index is
identified with a difference of Conley–Zehnder indices, which satisfy the same homotopy axiom
(`TauCeti.GLSymplectic.conleyZehnderIndex_eq_of_homotopy_of_not_hasEigenvalue_one`).

The orbits are fixed along the homotopy. This is the case of the model operators
`∂s + J₀ ∂t + S(s, t)` at the constant orbit `0` of Hamiltonians quadratic in the point whose
asymptotic symmetric matrices `S±` do not depend on `t` (the suspended vector fields are required
to be globally Lipschitz, which excludes `t`-dependent ones): these `S±` may then be deformed among
nondegenerate constant symmetric matrices.

The proof joins the two operators through model data: a constant compatible almost complex
structure `J₀`, `K_s = 0` and the continuation homotopy `K_t = H_{μ,(s, t)}` from `H₋_μ` to `H₊_μ`
(`TauCeti.Floer.continuationHomotopy`), which are cylindrical near the ends with radius `1` and
end Hamiltonians `H±_μ` for every `μ`. At `μ = 0` and at `μ = 1` the model data have the end
Hamiltonians of the given data, so the invariance under the data and under the map applies there.
Between them, the model data form a family whose end Hamiltonians move with `μ` while the orbits
stay nondegenerate, along which the Fredholm property and the index are constant
(`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_and_index_eq_of_family`). The slice
defects `∂t u - X_{H±_μ,t}(u)` tend to zero at the ends for every `μ` because the vector fields
`X_{H±_μ}` all agree along the orbits (`TauCeti.tendstoUniformlyOn_sliceDefect_of_apply_eq`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Fredholm index of `∂s + J ∂t + S(s, t)` and its
  identification with the Conley–Zehnder indices of the limits.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33, on the homotopy invariance of the index of operators with invertible limits.
-/

public section

noncomputable section

open Filter Set Function Topology
open scoped NNReal Manifold

namespace TauCeti.SymplecticForm


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The model data `(J₀, 0, H_{μ,(s, t)})`, with a constant compatible almost complex structure
and the continuation homotopy from `H₋_μ` to `H₊_μ`, are cylindrical near the ends with radius `1`
and end Hamiltonians `H±_μ`, along every map: this is
`TauCeti.Floer.isCylindricalNearEnds_continuationHomotopy` for the constant families `J± = J₀`. -/
private theorem isCylindricalNearEnds_continuationHomotopy_const {ω : SymplecticForm V}
    {J₀ : AlmostComplexStructure V} (hJ₀ : ω.Compatible J₀) {Hm Hp : ℝ → ℝ → V → ℝ}
    (hHm : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hm p.1 p.2.1 p.2.2)
    (hHp : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hp p.1 p.2.1 p.2.2) (μ : ℝ) (u : ℝ × ℝ → V) :
    Floer.IsCylindricalNearEnds (fun _ _ ↦ J₀) (fun _ _ ↦ 0)
      (Floer.continuationHomotopy (Hm μ) (Hp μ)) (fun _ _ ↦ J₀) (fun _ _ ↦ J₀) (Hm μ) (Hp μ) 1
      u := by
  have h := Floer.isCylindricalNearEnds_continuationHomotopy hJ₀ (Jm := fun _ _ ↦ J₀)
    (Jp := fun _ _ ↦ J₀) (hJmt := fun _ _ ↦ hJ₀.tames) (hJpt := fun _ _ ↦ hJ₀.tames)
    (Hm := Hm μ) (Hp := Hp μ) contDiff_const contDiff_const (hHm.comp (contDiff_prodMk_right μ))
    (hHp.comp (contDiff_prodMk_right μ)) u
  rwa [show Floer.continuationAlmostComplex hJ₀ (fun _ _ ↦ J₀) (fun _ _ ↦ J₀)
      (fun _ _ ↦ hJ₀.tames) (fun _ _ ↦ hJ₀.tames) = fun _ _ ↦ J₀ from
    funext₂ fun z x ↦ Floer.continuationAlmostComplex_self hJ₀ z x] at h

/-- Along a homotopy of time-dependent Hamiltonians `H_μ` of which `x` is an orbit for every
`μ ∈ [0, 1]`, the slice defects of `u` for every `H_μ` tend to zero at an end along which `u`
converges to `x` and its slice defect for `H_0` tends to zero: the vector fields `X_{H_μ}` all
agree along `x`. -/
private theorem tendstoUniformlyOn_sliceDefect_homotopy (ω : SymplecticForm V)
    {H : ℝ → ℝ → V → ℝ} (hH : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ H p.1 p.2.1 p.2.2) {x : ℝ → V}
    (hx : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt x (ω.hamiltonianVectorField (H μ t) (x t)) t)
    {u : ℝ × ℝ → V} {l : Filter ℝ} (hux : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 1))
    (hδ : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H 0 t)) u (s, t)) 0 l (Icc 0 1))
    {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1) :
    TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (H μ t)) u (s, t)) 0 l
        (Icc 0 1) := by
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hXc (ν : ℝ) : Continuous (uncurry fun t ↦ ω.hamiltonianVectorField (H ν t)) :=
    (ω.contDiff_hamiltonianVectorField_uncurry (n := 1) (K := H ν)
      (hH.comp (contDiff_prodMk_right ν))).continuous
  exact tendstoUniformlyOn_sliceDefect_of_apply_eq (hXc 0) (hXc μ)
    (continuous_iff_continuousAt.2 fun t ↦ (hx 0 h₀ t).continuousAt)
    (fun t ↦ (hx μ hμ t).unique (hx 0 h₀ t)) hux hδ

/-- The Fredholm property and the index are constant along the model data
`(J₀, 0, H_{μ,(s, t)})` of the homotopies `H±`, for `μ ∈ [0, 1]`, along a map `u` asymptotic to
the common orbits `x±`. -/
private theorem isFredholm_and_index_eq_of_homotopy_model (ω : SymplecticForm V)
    {J₀ : AlmostComplexStructure V} (hJ₀ : ω.Compatible J₀) {Hm Hp : ℝ → ℝ → V → ℝ}
    {u : ℝ × ℝ → V} (hu : ContDiff ℝ 1 u) {μ₀ μ₁ : ℝ} (hμ₀ : μ₀ ∈ Icc (0 : ℝ) 1)
    (hμ₁ : μ₁ ∈ Icc (0 : ℝ) 1)
    (hHm : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hm p.1 p.2.1 p.2.2)
    (hHp : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hp p.1 p.2.1 p.2.2)
    {Km : ℝ → ℝ≥0}
    (hXm : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Km μ) (ω.timeDependentHamiltonianSuspension (Hm μ)))
    {xm : ℝ → V}
    (hxm : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm μ t) (xm t)) t)
    (hndm : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hm μ) (hXm μ hμ) 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm μ₀ t)) u (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ → ℝ≥0}
    (hXp : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Kp μ) (ω.timeDependentHamiltonianSuspension (Hp μ)))
    {xp : ℝ → V}
    (hxp : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp μ t) (xp t)) t)
    (hndp : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hp μ) (hXp μ hμ) 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp μ₀ t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (Floer.continuationHomotopy (Hm μ₀) (Hp μ₀)) u).IsFredholm) :
    (ω.floerSobolevOperator (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (Floer.continuationHomotopy (Hm μ₁) (Hp μ₁)) u).IsFredholm ∧
      (ω.floerSobolevOperator (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (Floer.continuationHomotopy (Hm μ₁) (Hp μ₁)) u).index =
        (ω.floerSobolevOperator (fun _ _ ↦ J₀.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (Floer.continuationHomotopy (Hm μ₀) (Hp μ₀)) u).index :=
  isFredholm_floerSobolevOperator_and_index_eq_of_family ω
    (J := fun _ _ ↦ J₀) (Ks := fun _ _ ↦ 0)
    (Kt := fun p ↦ Floer.continuationHomotopy (Hm p.1) (Hp p.1) p.2)
    (Jm := fun _ _ _ ↦ J₀) (Jp := fun _ _ _ ↦ J₀) isPreconnected_Icc hμ₀ hμ₁
    (fun μ _ ↦ isCylindricalNearEnds_continuationHomotopy_const hJ₀ hHm hHp μ u) contDiff_const
    contDiff_const (Floer.contDiff_uncurry_continuationHomotopy_family hHm hHp) (fun _ _ ↦ hJ₀) hu
    hXm hxm hndm huxm hδm hXp hxp hndp huxp hδp h

/-- The Fredholm property and the index pass from the data `(J, K_s, K_t)` along `u`, with end
Hamiltonians `H±_0`, to the data `(J', K'_s, K'_t)` along `u'`, with end Hamiltonians `H±_1`,
through the model data of the homotopies `H±`. -/
private theorem isFredholm_iff_and_index_eq_of_homotopy (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp (Hm 0) (Hp 0) R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' (Hm 1) (Hp 1) R' u')
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs' : ContDiff ℝ 2 (uncurry Ks')) (hKt' : ContDiff ℝ 2 (uncurry Kt'))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hJ'c : ∀ z y, ω.Compatible (J' z y))
    (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    (hHm : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hm p.1 p.2.1 p.2.2)
    (hHp : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hp p.1 p.2.1 p.2.2)
    {Km : ℝ → ℝ≥0}
    (hXm : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Km μ) (ω.timeDependentHamiltonianSuspension (Hm μ)))
    {xm : ℝ → V}
    (hxm : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm μ t) (xm t)) t)
    (hndm : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hm μ) (hXm μ hμ) 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm 0 t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hu'xm : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xm atBot (Icc 0 1))
    (hδ'm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm 1 t)) u' (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ → ℝ≥0}
    (hXp : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Kp μ) (ω.timeDependentHamiltonianSuspension (Hp μ)))
    {xp : ℝ → V}
    (hxp : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp μ t) (xp t)) t)
    (hndp : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hp μ) (hXp μ hμ) 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp 0 t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hu'xp : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xp atTop (Icc 0 1))
    (hδ'p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp 1 t)) u' (s, t)) 0 atTop
        (Icc 0 1)) :
    ((ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).IsFredholm ↔
      (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
        u').IsFredholm) ∧
    ((ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).IsFredholm →
      (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
          u').index =
        (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
          u).index) := by
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- The model data `(J₀, 0, H_{μ,(s, t)})` at the parameter `μ`, along `v`.
  set J₀ := J 0 0
  have hcylD (μ : ℝ) (v : ℝ × ℝ → V) :=
    isCylindricalNearEnds_continuationHomotopy_const (hJc 0 0) hHm hHp μ v
  have hKtD (μ : ℝ) : ContDiff ℝ 2 (uncurry (Floer.continuationHomotopy (Hm μ) (Hp μ))) :=
    Floer.contDiff_uncurry_continuationHomotopy (hHm.comp (contDiff_prodMk_right μ))
      (hHp.comp (contDiff_prodMk_right μ))
  have hJ₀ : ContDiff ℝ 1 fun _ : (ℝ × ℝ) × V ↦ J₀.toLinearMap.toContinuousLinearMap :=
    contDiff_const
  have hKsD : ContDiff ℝ 2 (uncurry fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ)) := contDiff_const
  have hJ₀c : ∀ (_ : ℝ × ℝ) (_ : V), ω.Compatible J₀ := fun _ _ ↦ hJc 0 0
  have hδm₁ := tendstoUniformlyOn_sliceDefect_homotopy ω hHm hxm huxm hδm h₁
  have hδp₁ := tendstoUniformlyOn_sliceDefect_homotopy ω hHp hxp huxp hδp h₁
  have hfam₀₁ := isFredholm_and_index_eq_of_homotopy_model ω (hJc 0 0) hu h₀ h₁ hHm hHp hXm hxm
    hndm huxm hδm hXp hxp hndp huxp hδp
  have hfam₁₀ := isFredholm_and_index_eq_of_homotopy_model ω (hJc 0 0) hu h₁ h₀ hHm hHp hXm hxm
    hndm huxm hδm₁ hXp hxp hndp huxp hδp₁
  -- At `μ = 0`: the given data along `u` and the model data along `u`.
  have hdata₀ := ω.isFredholm_floerSobolevOperator_iff_of_cylindrical_data hcyl (hcylD 0 u) hJ hKs
    hKt hJ₀ hKsD (hKtD 0) hJc hJ₀c hu (hXm 0 h₀) (hxm 0 h₀) (hndm 0 h₀) huxm hδm (hXp 0 h₀)
    (hxp 0 h₀) (hndp 0 h₀) huxp hδp
  have hidx₀ := ω.index_floerSobolevOperator_eq_of_cylindrical_data hcyl (hcylD 0 u) hJ hKs hKt
    hJ₀ hKsD (hKtD 0) hJc hJ₀c hu (hXm 0 h₀) (hxm 0 h₀) (hndm 0 h₀) huxm hδm (hXp 0 h₀)
    (hxp 0 h₀) (hndp 0 h₀) huxp hδp
  -- At `μ = 1`: the model data along `u` and along `u'`.
  have hmap₁ := ω.isFredholm_floerSobolevOperator_iff_of_cylindrical (hcylD 1 u) hJ₀ hKsD (hKtD 1)
    hJ₀c hu hu' (hXm 1 h₁) (hxm 1 h₁) (hndm 1 h₁) huxm hδm₁ hu'xm hδ'm (hXp 1 h₁) (hxp 1 h₁)
    (hndp 1 h₁) huxp hδp₁ hu'xp hδ'p
  have hidx₁ := ω.index_floerSobolevOperator_eq_of_cylindrical (hcylD 1 u) hJ₀ hKsD (hKtD 1)
    hJ₀c hu hu' (hXm 1 h₁) (hxm 1 h₁) (hndm 1 h₁) huxm hδm₁ hu'xm hδ'm (hXp 1 h₁) (hxp 1 h₁)
    (hndp 1 h₁) huxp hδp₁ hu'xp hδ'p
  -- At `μ = 1`: the model data along `u'` and the given data along `u'`.
  have hdata₁ := ω.isFredholm_floerSobolevOperator_iff_of_cylindrical_data (hcylD 1 u') hcyl'
    hJ₀ hKsD (hKtD 1) hJ' hKs' hKt' hJ₀c hJ'c hu' (hXm 1 h₁) (hxm 1 h₁) (hndm 1 h₁) hu'xm hδ'm
    (hXp 1 h₁) (hxp 1 h₁) (hndp 1 h₁) hu'xp hδ'p
  have hidx₁' := ω.index_floerSobolevOperator_eq_of_cylindrical_data (hcylD 1 u') hcyl' hJ₀ hKsD
    (hKtD 1) hJ' hKs' hKt' hJ₀c hJ'c hu' (hXm 1 h₁) (hxm 1 h₁) (hndm 1 h₁) hu'xm hδ'm
    (hXp 1 h₁) (hxp 1 h₁) (hndp 1 h₁) hu'xp hδ'p
  refine ⟨hdata₀.trans (Iff.trans ⟨fun h ↦ (hfam₀₁ h).1, fun h ↦ (hfam₁₀ h).1⟩
    (hmap₁.trans hdata₁)), fun h ↦ ?_⟩
  have hF₁ := hfam₀₁ (hdata₀.1 h)
  rw [hidx₁' (hmap₁.1 hF₁.1), hidx₁ hF₁.1, hF₁.2, hidx₀ h]

/-- **The Fredholm property of the linearized Floer operator is invariant under homotopies of the
end Hamiltonians.** Let `H±_μ`, `μ ∈ ℝ`, be homotopies of time-dependent Hamiltonians, jointly `C²`
in the parameter, the time and the point, such that for every `μ ∈ [0, 1]` the suspended vector
fields of `H₋_μ` and `H₊_μ` are globally Lipschitz and the loops `x₋` and `x₊` are nondegenerate
one-periodic orbits of `H₋_μ` and `H₊_μ`. Let `(J, K_s, K_t)` and `(J', K'_s, K'_t)` be Floer
data that are `C¹` (with `C²` Hamiltonians) on the whole cylinder, compatible with `ω`, and
cylindrical near the ends with end Hamiltonians `H±_0` and `H±_1` respectively. Let `u` and `u'`
be `C¹` maps whose loops converge uniformly to `x₋` at `-∞` and `x₊` at `+∞`, with slice defects
for the end Hamiltonians of their data tending uniformly to zero there. Then `D_u` for the first
data is Fredholm if and only if `D_{u'}` for the second data is. -/
theorem isFredholm_floerSobolevOperator_iff_of_homotopy (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp (Hm 0) (Hp 0) R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' (Hm 1) (Hp 1) R' u')
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs' : ContDiff ℝ 2 (uncurry Ks')) (hKt' : ContDiff ℝ 2 (uncurry Kt'))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hJ'c : ∀ z y, ω.Compatible (J' z y))
    (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    (hHm : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hm p.1 p.2.1 p.2.2)
    (hHp : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hp p.1 p.2.1 p.2.2)
    {Km : ℝ → ℝ≥0}
    (hXm : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Km μ) (ω.timeDependentHamiltonianSuspension (Hm μ)))
    {xm : ℝ → V}
    (hxm : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm μ t) (xm t)) t)
    (hndm : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hm μ) (hXm μ hμ) 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm 0 t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hu'xm : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xm atBot (Icc 0 1))
    (hδ'm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm 1 t)) u' (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ → ℝ≥0}
    (hXp : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Kp μ) (ω.timeDependentHamiltonianSuspension (Hp μ)))
    {xp : ℝ → V}
    (hxp : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp μ t) (xp t)) t)
    (hndp : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hp μ) (hXp μ hμ) 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp 0 t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hu'xp : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xp atTop (Icc 0 1))
    (hδ'p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp 1 t)) u' (s, t)) 0 atTop
        (Icc 0 1)) :
    (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).IsFredholm ↔
      (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
        u').IsFredholm :=
  (isFredholm_iff_and_index_eq_of_homotopy ω hcyl hcyl' hJ hKs hKt hJ' hKs' hKt' hJc hJ'c hu hu'
    hHm hHp hXm hxm hndm huxm hδm hu'xm hδ'm hXp hxp hndp huxp hδp hu'xp hδ'p).1

/-- **The index of the linearized Floer operator is invariant under homotopies of the end
Hamiltonians.** Under the hypotheses of
`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_of_homotopy`, if `D_u` for the data
`(J, K_s, K_t)` with end Hamiltonians `H±_0` is Fredholm, then `D_{u'}` for the data
`(J', K'_s, K'_t)` with end Hamiltonians `H±_1` has the same index. -/
theorem index_floerSobolevOperator_eq_of_homotopy (ω : SymplecticForm V)
    {J J' : ℝ × ℝ → V → AlmostComplexStructure V} {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ}
    {Hm Hp : ℝ → ℝ → V → ℝ} {Jm Jp Jm' Jp' : ℝ → V → AlmostComplexStructure V} {R R' : ℝ}
    {u u' : ℝ × ℝ → V}
    (hcyl : Floer.IsCylindricalNearEnds J Ks Kt Jm Jp (Hm 0) (Hp 0) R u)
    (hcyl' : Floer.IsCylindricalNearEnds J' Ks' Kt' Jm' Jp' (Hm 1) (Hp 1) R' u')
    (hJ : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs : ContDiff ℝ 2 (uncurry Ks)) (hKt : ContDiff ℝ 2 (uncurry Kt))
    (hJ' : ContDiff ℝ 1 fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hKs' : ContDiff ℝ 2 (uncurry Ks')) (hKt' : ContDiff ℝ 2 (uncurry Kt'))
    (hJc : ∀ z y, ω.Compatible (J z y)) (hJ'c : ∀ z y, ω.Compatible (J' z y))
    (hu : ContDiff ℝ 1 u) (hu' : ContDiff ℝ 1 u')
    (hHm : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hm p.1 p.2.1 p.2.2)
    (hHp : ContDiff ℝ 2 fun p : ℝ × ℝ × V ↦ Hp p.1 p.2.1 p.2.2)
    {Km : ℝ → ℝ≥0}
    (hXm : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Km μ) (ω.timeDependentHamiltonianSuspension (Hm μ)))
    {xm : ℝ → V}
    (hxm : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xm (ω.hamiltonianVectorField (Hm μ t) (xm t)) t)
    (hndm : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hm μ) (hXm μ hμ) 0 1) (xm 0))
    (huxm : TendstoUniformlyOn (fun s t ↦ u (s, t)) xm atBot (Icc 0 1))
    (hδm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm 0 t)) u (s, t)) 0 atBot
        (Icc 0 1))
    (hu'xm : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xm atBot (Icc 0 1))
    (hδ'm : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hm 1 t)) u' (s, t)) 0 atBot
        (Icc 0 1))
    {Kp : ℝ → ℝ≥0}
    (hXp : ∀ μ ∈ Icc (0 : ℝ) 1, LipschitzWith (Kp μ) (ω.timeDependentHamiltonianSuspension (Hp μ)))
    {xp : ℝ → V}
    (hxp : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t, HasDerivAt xp (ω.hamiltonianVectorField (Hp μ t) (xp t)) t)
    (hndp : ∀ μ (hμ : μ ∈ Icc (0 : ℝ) 1),
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (Hp μ) (hXp μ hμ) 0 1) (xp 0))
    (huxp : TendstoUniformlyOn (fun s t ↦ u (s, t)) xp atTop (Icc 0 1))
    (hδp : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp 0 t)) u (s, t)) 0 atTop
        (Icc 0 1))
    (hu'xp : TendstoUniformlyOn (fun s t ↦ u' (s, t)) xp atTop (Icc 0 1))
    (hδ'p : TendstoUniformlyOn
      (fun s t ↦ sliceDefect (fun t ↦ ω.hamiltonianVectorField (Hp 1 t)) u' (s, t)) 0 atTop
        (Icc 0 1))
    (h : (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
      u).IsFredholm) :
    (ω.floerSobolevOperator (fun w y ↦ (J' w y).toLinearMap.toContinuousLinearMap) Ks' Kt'
        u').index =
      (ω.floerSobolevOperator (fun w y ↦ (J w y).toLinearMap.toContinuousLinearMap) Ks Kt
        u).index :=
  (isFredholm_iff_and_index_eq_of_homotopy ω hcyl hcyl' hJ hKs hKt hJ' hKs' hKt' hJc hJ'c hu hu'
    hHm hHp hXm hxm hndm huxm hδm hu'xm hδ'm hXp hxp hndp huxp hδp hu'xp hδ'p).2 h

end TauCeti.SymplecticForm
