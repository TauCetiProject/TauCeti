/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Dimension
public import TauCeti.FieldTheory.FunctionField.Differential.LocalComponent

/-!
# Nonvanishing of local components of Weil differentials

Every local component of a nonzero Weil differential on an algebraic function field is nonzero.
Consequently, fixing any one place `P`, the map `ω ↦ ω_P` is injective on the space of Weil
differentials: one local component determines the global differential.

The key point is that allowing a double pole at `P` strictly enlarges the space of regular Weil
differentials.  Indeed,

`dim_k Ω_F(-2P) = 2 deg P - 1 + g > g = dim_k Ω_F(0)`.

Thus some differential in `Ω_F(-2P)` is not regular.  Its local component at `P` cannot vanish,
because the local-component characterization of the filtration would then make it regular after
all.  Since the full space of Weil differentials is one-dimensional over `F`, multiplication by a
function carries this witness to any prescribed nonzero differential, and multiplication cannot
create a zero local component.

This is the nonvanishing assertion and the final clause of Stichtenoth, *Algebraic Function Fields
and Codes*, 2nd ed., Proposition 1.7.3(a).  It is the local input for defining the order of a Weil
differential and for comparing Weil differentials with Kähler differentials through residues.

## Main results

* `TauCeti.repartitionDualComponent_ne_zero`: every local component of a nonzero Weil differential
  is nonzero.
* `TauCeti.repartitionDualComponent_eq_zero_iff`: a Weil differential is zero exactly when its
  local component at one fixed place is zero.
* `TauCeti.repartitionDualComponent_eq_iff`: two Weil differentials are equal exactly when their
  local components at one fixed place are equal.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.3(a).
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- At every place of an algebraic function field with exact constants, some Weil differential
has a nonzero local component.

The witness can be taken from `Ω_F(-2P)`: this space has dimension
`2 * deg P - 1 + g`, strictly larger than the `g`-dimensional space `Ω_F(0)` of regular
differentials. -/
private theorem exists_repartitionDualComponent_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (P : Place k F) :
    ∃ ω : Module.Dual k ↥(repartitionSpace k F),
      ω ∈ weilDifferentialSpace k F ∧ repartitionDualComponent ω P ≠ 0 := by
  let D : Divisor k F := (-2 : ℤ) • WeilDivisor.ofPoint P
  have hDneg : D < 0 := WeilDivisor.zsmul_ofPoint_lt_zero P (by omega)
  have hle : weilDifferentialFiltration (0 : Divisor k F) ≤
      weilDifferentialFiltration D :=
    weilDifferentialFiltration_antitone hDneg.le
  have hfdD := finiteDimensional_weilDifferentialFiltration hF hex D
  have hdimD := finrank_weilDifferentialFiltration hF hex D
  have hdim0 := finrank_weilDifferentialFiltration_zero hF hex
  have hP : (1 : ℤ) ≤ P.degree := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hdimlt : Module.finrank k ↥(weilDifferentialFiltration (0 : Divisor k F)) <
      Module.finrank k ↥(weilDifferentialFiltration D) := by
    rw [hdim0]
    rw [Divisor.indexOfSpecialty_def,
      Divisor.dim_eq_zero_of_lt_zero hF hDneg, Divisor.degree_zsmul,
      Divisor.degree_ofPoint] at hdimD
    dsimp [D] at hdimD
    have hdimD' : (genus k F : ℤ) <
        Module.finrank k ↥(weilDifferentialFiltration D) := by
      rw [hdimD]
      omega
    exact_mod_cast hdimD'
  have hlt : weilDifferentialFiltration (0 : Divisor k F) <
      weilDifferentialFiltration D :=
    Submodule.lt_of_le_of_finrank_lt_finrank hle hdimlt
  obtain ⟨ω, hωD, hω0⟩ := SetLike.exists_of_lt hlt
  have hωspace : ω ∈ weilDifferentialSpace k F :=
    weilDifferentialFiltration_le_weilDifferentialSpace D hωD
  refine ⟨ω, hωspace, fun hcomponent ↦ hω0 ?_⟩
  rw [mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero hωspace]
  intro Q x hx
  rcases eq_or_ne Q P with rfl | hQP
  · rw [hcomponent]
    exact LinearMap.zero_apply _
  · exact repartitionDualComponent_apply_eq_zero_of_le hωD Q (by
      simpa [D, WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_of_ne hQP] using hx)

/-- **Every local component of a nonzero Weil differential is nonzero**
(Stichtenoth, Proposition 1.7.3(a)). -/
theorem repartitionDualComponent_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (hω0 : ω ≠ 0) (P : Place k F) :
    repartitionDualComponent ω P ≠ 0 := by
  obtain ⟨η, hη, hηP⟩ := exists_repartitionDualComponent_ne_zero hF hex P
  obtain ⟨c, hc⟩ := exists_repartitionDualMul_eq hF hex hω hω0 hη
  intro hωP
  apply hηP
  ext x
  rw [← hc, repartitionDualComponent_repartitionDualMul, hωP, LinearMap.zero_apply,
    LinearMap.zero_apply]

/-- A Weil differential is zero exactly when its local component at one fixed place is zero. -/
theorem repartitionDualComponent_eq_zero_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (P : Place k F) :
    repartitionDualComponent ω P = 0 ↔ ω = 0 := by
  refine ⟨fun h ↦ not_ne_iff.mp fun hω0 ↦
    repartitionDualComponent_ne_zero hF hex hω hω0 P h, ?_⟩
  rintro rfl
  ext x
  simp

/-- **One local component determines a Weil differential**: two Weil differentials are equal if
and only if their local components at any one fixed place are equal. -/
theorem repartitionDualComponent_eq_iff (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {ω η : Module.Dual k ↥(repartitionSpace k F)}
    (hω : ω ∈ weilDifferentialSpace k F) (hη : η ∈ weilDifferentialSpace k F)
    (P : Place k F) :
    repartitionDualComponent ω P = repartitionDualComponent η P ↔ ω = η := by
  constructor
  · intro hcomponent
    have hsub : repartitionDualComponent (ω - η) P = 0 := by
      ext x
      have hx := LinearMap.congr_fun hcomponent x
      rw [repartitionDualComponent_apply, LinearMap.sub_apply, LinearMap.zero_apply]
      exact sub_eq_zero.mpr (by simpa only [repartitionDualComponent_apply] using hx)
    exact sub_eq_zero.mp <|
      (repartitionDualComponent_eq_zero_iff hF hex (Submodule.sub_mem _ hω hη) P).mp hsub
  · rintro rfl
    rfl

end TauCeti
