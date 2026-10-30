/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# Noncommutative changes of section

A kernel-valued function changes a section of a group extension by left multiplication.
The conjugation maps and factors transform by the noncommutative gauge formulas, with
no centrality or commutativity assumption on the kernel. Every change of section arises
uniquely this way, through `TauCeti.GroupExtension.sectionDiff`.

A normalized section can be changed into a splitting exactly when a normalized gauge
makes all its transformed factors equal to one. This criterion applies in particular to
extensions with a division-algebra unit group as kernel, where abelian second cohomology
does not describe the obstruction.

## References

G. Karpilovsky, *Projective Representations of Finite Groups*, Marcel Dekker (1985), Ch. 1.
-/

public section

namespace GroupExtension.Section

open TauCeti.GroupExtension

variable {M E G : Type*} [Group M] [Group E] [Group G]
  {S : GroupExtension M E G}

/-- Change a section by multiplying on the left by a kernel-valued function. -/
def gauge (σ : S.Section) (b : G → M) : S.Section where
  toFun g := S.inl (b g) * σ g
  rightInverse_rightHom g := by simp

@[simp]
theorem gauge_apply (σ : S.Section) (b : G → M) (g : G) :
    σ.gauge b g = S.inl (b g) * σ g := (rfl)

@[simp]
theorem gauge_one (σ : S.Section) : σ.gauge 1 = σ := by
  apply DFunLike.ext
  intro g
  simp

/-- Successive changes of section multiply their gauges in the same order as their
left multiplication on the section. -/
@[simp]
theorem gauge_gauge (σ : S.Section) (b c : G → M) :
    (σ.gauge b).gauge c = σ.gauge (c * b) := by
  apply DFunLike.ext
  intro g
  simp [mul_assoc]

/-- Normalization of the section is preserved exactly by normalized gauges. -/
theorem gauge_one_eq_one_iff (σ : S.Section) (hσ : σ 1 = 1) (b : G → M) :
    σ.gauge b 1 = 1 ↔ b 1 = 1 := by
  rw [gauge_apply, hσ, mul_one, ← map_one S.inl, S.inl_injective.eq_iff]

/-- The section difference recovers the unique gauge relating two sections. -/
@[simp]
theorem sectionDiff_gauge (σ : S.Section) (b : G → M) :
    sectionDiff (σ.gauge b) σ = b := by
  funext g
  apply S.inl_injective
  simp

/-- Every section is obtained from any other section by its kernel-valued difference. -/
@[simp]
theorem gauge_sectionDiff (σ τ : S.Section) : σ.gauge (sectionDiff τ σ) = τ := by
  apply DFunLike.ext
  intro g
  simp

/-- Changing the section conjugates each kernel automorphism by the gauge value. -/
theorem conjAct_gauge (σ : S.Section) (b : G → M) (g : G) (m : M) :
    S.conjAct (σ.gauge b g) m = b g * S.conjAct (σ g) m * (b g)⁻¹ := by
  apply S.inl_injective
  rw [GroupExtension.inl_conjAct_comm, gauge_apply]
  simp only [map_mul, map_inv, GroupExtension.inl_conjAct_comm]
  group

/-- The noncommutative transformation law for the factor of a section. The conjugation
is that of the original section; it need not be an action of the quotient group. -/
theorem factorSetFun_gauge (σ : S.Section) (b : G → M) (g h : G) :
    factorSetFun (σ.gauge b) (g, h) =
      b g * S.conjAct (σ g) (b h) * factorSetFun σ (g, h) * (b (g * h))⁻¹ := by
  apply S.inl_injective
  simp only [inl_factorSetFun, gauge_apply, map_mul, map_inv,
    GroupExtension.inl_conjAct_comm]
  group

/-- A section is multiplicative exactly when its factor is identically one. -/
theorem factorSetFun_eq_one_iff (σ : S.Section) :
    (∀ g h, factorSetFun σ (g, h) = 1) ↔ ∀ g h, σ (g * h) = σ g * σ h := by
  constructor
  · intro h g j
    simpa [h] using (section_mul σ g j).symm
  · intro h g j
    apply S.inl_injective
    simp [h]

/-- A section with trivial factor gives a splitting of the group extension. -/
def splittingOfFactorSetEqOne (σ : S.Section) (hσ : ∀ g h, factorSetFun σ (g, h) = 1) :
    S.Splitting where
  __ := MonoidHom.mk' (σ : G → E) ((σ.factorSetFun_eq_one_iff).mp hσ)
  rightInverse_rightHom := σ.rightInverse_rightHom

@[simp]
theorem splittingOfFactorSetEqOne_apply (σ : S.Section)
    (hσ : ∀ g h, factorSetFun σ (g, h) = 1) (g : G) :
    σ.splittingOfFactorSetEqOne hσ g = σ g := (rfl)

/-- An extension splits exactly when a normalized gauge neutralizes the factors of
any specified normalized section. The kernel may be nonabelian. -/
theorem nonempty_splitting_iff_exists_gauge (σ : S.Section) (hσ : σ 1 = 1) :
    Nonempty S.Splitting ↔ ∃ b : G → M, b 1 = 1 ∧
      ∀ g h, b g * S.conjAct (σ g) (b h) * factorSetFun σ (g, h) *
        (b (g * h))⁻¹ = 1 := by
  constructor
  · rintro ⟨s⟩
    refine ⟨sectionDiff s.toSection σ, ?_, ?_⟩
    · apply S.inl_injective
      simp [hσ]
    · intro g h
      rw [← factorSetFun_gauge, gauge_sectionDiff]
      exact (s.toSection.factorSetFun_eq_one_iff).mpr (fun g h => map_mul s g h) g h
  · rintro ⟨b, hb, h⟩
    exact ⟨(σ.gauge b).splittingOfFactorSetEqOne (by
      intro g j
      rw [factorSetFun_gauge]
      exact h g j)⟩

end GroupExtension.Section
