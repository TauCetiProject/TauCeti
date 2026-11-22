/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Cocompact
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Maps.OpenQuotient
import TauCeti.MeasureTheory.Integral.ContinuousMap
import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Real characters of central extensions of compact groups

Let `G` be a locally compact group and `Γ` a discrete central subgroup with compact
quotient `G ⧸ Γ`, so that `G` is a central extension of the compact group `G ⧸ Γ` by `Γ`. This
file shows that every homomorphism `χ : Γ → ℝ` extends to a continuous homomorphism `G → ℝ`
(`Subgroup.exists_continuous_monoidHom_comp_subtype_eq`). Consequently, if `G` is connected and has
no nonzero continuous homomorphism to `ℝ`, then `Γ` is finite
(`Subgroup.finite_of_forall_continuous_eq_one`), and so `G` itself is compact
(`Subgroup.compactSpace_of_forall_continuous_eq_one`).

The extension is an average over the compact group `G ⧸ Γ`. Write `χ` as the coboundary of a
continuous `f : G → ℝ`, so that `f (g γ) = f g + χ γ`
(`Subgroup.exists_continuousMap_mul_eq_add`). Then `f (g h) - f h` depends only on the coset
`h Γ`, and its average over `h Γ ∈ G ⧸ Γ` against the Haar probability measure,

`F g = ∫ (f (g h) - f h) d(h Γ)`,

is additive in `g` by left invariance of Haar measure and continuous by compactness. Since `Γ` is
central, `f (γ h) - f h = f (h γ) - f h = χ γ`, so `F` extends `χ`.

For the finiteness statement, `Γ` is finitely generated (`Subgroup.fg_of_compactSpace_quotient`)
and commutative. An element `γ` of infinite order generates a copy of `ℤ`, and the homomorphism
sending `γ` to `1` extends to all of `Γ` because `ℝ` is divisible, hence injective as an abelian
group; its continuous extension to `G` is then nonzero. So `Γ` is a finitely generated torsion
abelian group, which is finite.

This is the group-theoretic half of Weyl's theorem that the universal cover `G'` of a compact
connected Lie group `G` with semisimple Lie algebra is compact: the kernel of `G' → G` is a
discrete central subgroup with compact quotient `G`. The Lie-theoretic half, that a connected Lie
group with perfect Lie algebra has no nonzero continuous homomorphism to `ℝ`, is not proved here.

## Main results

* `Subgroup.exists_continuous_monoidHom_comp_subtype_eq`: real characters extend from a discrete
  central subgroup with compact quotient.
* `Subgroup.finite_of_forall_continuous_eq_one`: a discrete central subgroup with compact quotient
  of a connected locally compact group without nonzero continuous real characters is finite.
* `Subgroup.compactSpace_of_forall_continuous_eq_one`: such a group is compact.

## References

* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups*, Springer (2012), Chapter 12,
  for Weyl's theorem on compact semisimple Lie groups.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Graduate Texts in
  Mathematics 98, Springer (1985), Chapter V.
-/

public section

open MeasureTheory

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
  [CompactSpace (G ⧸ Γ)]

omit [LocallyCompactSpace G] [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] in
/-- If `f (g γ) = f g + χ γ`, the difference `f (g h) - f h` only depends on `g` and the coset
`h Γ`, continuously. -/
private theorem exists_continuousMap_quotient_eq_sub (f : C(G, ℝ)) {χ : Γ →* Multiplicative ℝ}
    (hf : ∀ (g : G) (γ : Γ), f (g * γ) = f g + (χ γ).toAdd) :
    ∃ Φ : C(G × (G ⧸ Γ), ℝ), ∀ g h : G, Φ (g, (h : G ⧸ Γ)) = f (g * h) - f h := by
  set Φ : G × (G ⧸ Γ) → ℝ := fun p ↦ f (p.1 * p.2.out) - f p.2.out
  have hΦ : ∀ g h : G, Φ (g, (h : G ⧸ Γ)) = f (g * h) - f h := by
    intro g h
    obtain ⟨γ, hγ⟩ : ∃ γ : Γ, (h : G ⧸ Γ).out = h * γ :=
      ⟨⟨h⁻¹ * (h : G ⧸ Γ).out, QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm⟩, by simp⟩
    simp only [Φ]
    rw [hγ, ← mul_assoc, hf, hf]
    ring
  refine ⟨⟨Φ, ?_⟩, hΦ⟩
  rw [← (IsOpenQuotientMap.id.prodMap QuotientGroup.isOpenQuotientMap_mk).continuous_comp_iff]
  convert (f.continuous.comp continuous_mul).sub (f.continuous.comp continuous_snd) using 1
  ext ⟨g, h⟩
  exact hΦ g h

/-- **Real characters extend from a discrete central subgroup with compact quotient.** Let `Γ` be a
discrete central subgroup of a locally compact group `G` with `G ⧸ Γ` compact. Every
homomorphism `χ : Γ → ℝ` is the restriction of a continuous homomorphism `F : G → ℝ`. -/
theorem exists_continuous_monoidHom_comp_subtype_eq (hΓ : Γ ≤ center G)
    (χ : Γ →* Multiplicative ℝ) :
    ∃ F : G →* Multiplicative ℝ, Continuous F ∧ F.comp Γ.subtype = χ := by
  have := normal_of_le_center hΓ
  obtain ⟨f, hf⟩ := Γ.exists_continuousMap_mul_eq_add χ
  obtain ⟨Φ, hΦ⟩ := Γ.exists_continuousMap_quotient_eq_sub f hf
  let _ : MeasurableSpace (G ⧸ Γ) := borel _
  have _ : BorelSpace (G ⧸ Γ) := ⟨rfl⟩
  set μ := TauCeti.haarProb (G ⧸ Γ)
  have hint : ∀ (g : G) {k : G ⧸ Γ → G ⧸ Γ}, Continuous k →
      Integrable (fun y ↦ Φ (g, k y)) μ := fun g k hk ↦
    (Φ.continuous.comp (continuous_const.prodMk hk)).integrable_of_compactSpace
  set F₀ : G → ℝ := fun g ↦ ∫ y, Φ (g, y) ∂μ
  -- Additivity, from the cocycle identity of `Φ` and left invariance of Haar measure.
  have hadd : ∀ g₁ g₂, F₀ (g₁ * g₂) = F₀ g₁ + F₀ g₂ := by
    intro g₁ g₂
    have hsplit : ∀ y, Φ (g₁ * g₂, y) = Φ (g₁, (g₂ : G ⧸ Γ) * y) + Φ (g₂, y) := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, hΦ, hΦ, hΦ, mul_assoc]
      ring
    simp only [F₀, hsplit]
    rw [integral_add (f := fun y ↦ Φ (g₁, (g₂ : G ⧸ Γ) * y)) (g := fun y ↦ Φ (g₂, y))
        (hint g₁ (continuous_const_mul _)) (hint g₂ continuous_id),
      integral_mul_left_eq_self (fun y ↦ Φ (g₁, y))]
  -- On the central subgroup `Γ`, the integrand is the constant `χ γ`.
  have hΓF : ∀ γ : Γ, F₀ γ = (χ γ).toAdd := by
    intro γ
    have hconst : ∀ y, Φ ((γ : G), y) = (χ γ).toAdd := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
      rw [hΦ, ← mem_center_iff.mp (hΓ γ.property) h, hf]
      ring
    simp [F₀, hconst]
  have hcont : Continuous F₀ :=
    TauCeti.continuous_integral_continuousMap.comp Φ.curry.continuous
  refine ⟨MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (F₀ g)) fun g₁ g₂ ↦ by
    rw [hadd, ofAdd_add], continuous_ofAdd.comp hcont, MonoidHom.ext fun γ ↦ ?_⟩
  simp [hΓF]

/-- **A central extension of a compact group without real characters has finite kernel.** Let `Γ`
be a discrete central subgroup of a connected locally compact group `G`, with `G ⧸ Γ`
compact. If every continuous homomorphism `G → ℝ` is trivial, then `Γ` is finite. -/
theorem finite_of_forall_continuous_eq_one [ConnectedSpace G] (hΓ : Γ ≤ center G)
    (h : ∀ F : G →* Multiplicative ℝ, Continuous F → F = 1) : Finite Γ := by
  have := Γ.fg_of_compactSpace_quotient
  let _ : CommGroup Γ :=
    { (inferInstance : Group Γ) with
      mul_comm := fun a b ↦ Subtype.ext (mem_center_iff.mp (hΓ b.property) a) }
  refine CommGroup.finite_of_fg_isMulTorsion _ fun γ ↦ ?_
  by_contra hγ
  -- The homomorphism `γ ↦ 1` on `⟨γ⟩ ≅ ℤ` extends to `Γ`, since `ℝ` is divisible.
  obtain ⟨χ, hχ⟩ := (Module.Baer.of_divisible ℝ).extension_property_addMonoidHom
    (zmultiplesHom (Additive Γ) (Additive.ofMul γ))
    (fun m n hmn ↦ injective_zpow_iff_not_isOfFinOrder.mpr hγ <| Additive.ofMul.injective <| by
      rw [ofMul_zpow, ofMul_zpow]
      simpa using hmn)
    (Int.castAddHom ℝ)
  have hχγ : χ (Additive.ofMul γ) = 1 := by simpa using DFunLike.congr_fun hχ 1
  obtain ⟨F, hFc, hF⟩ :=
    Γ.exists_continuous_monoidHom_comp_subtype_eq hΓ (AddMonoidHom.toMultiplicativeRight χ)
  have hFγ := DFunLike.congr_fun hF γ
  rw [h F hFc] at hFγ
  simpa [hχγ] using congrArg Multiplicative.toAdd hFγ

/-- **A central extension of a compact group without real characters is compact.** Let `Γ` be a
discrete central subgroup of a connected locally compact group `G`, with `G ⧸ Γ`
compact. If every continuous homomorphism `G → ℝ` is trivial, then `G` is compact: it is covered
by the translates `K γ` of a compact set `K` by the finitely many elements `γ` of `Γ`. -/
theorem compactSpace_of_forall_continuous_eq_one [ConnectedSpace G] (hΓ : Γ ≤ center G)
    (h : ∀ F : G →* Multiplicative ℝ, Continuous F → F = 1) : CompactSpace G := by
  have := Γ.finite_of_forall_continuous_eq_one hΓ h
  obtain ⟨U, K, -, -, hK, hUK, hcov⟩ := Γ.exists_isOpen_isCompact_forall_exists_mul_mem
  have hcover : (⋃ γ : Γ, (· * (γ : G)⁻¹) '' K) = Set.univ :=
    Set.eq_univ_of_forall fun g ↦ by
      obtain ⟨γ, hγΓ, hgγ⟩ := hcov g
      exact Set.mem_iUnion.mpr ⟨⟨γ, hγΓ⟩, g * γ, hUK hgγ, mul_inv_cancel_right g γ⟩
  exact ⟨hcover ▸ isCompact_iUnion fun γ ↦ hK.image (continuous_mul_const _)⟩

end Subgroup
