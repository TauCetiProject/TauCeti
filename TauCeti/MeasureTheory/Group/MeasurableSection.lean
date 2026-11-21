/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Borel sections of homomorphisms from local sections

Let `p : E →* G` be a surjective homomorphism onto a topological group, for instance the
projection of a central extension of `G` by the circle, and let `σ` be a section of `p` defined
only near the identity: `p (σ g) = g` for `g` in a neighbourhood `V` of `1`. When `G` is Lindelöf,
in particular second countable, the translates `g • V` have a countable subcover `gₙ • V`. Choosing
lifts `ĝₙ` of the `gₙ` and putting `s g = ĝₙ * σ (gₙ⁻¹ * g)`, for the least `n` with `g ∈ gₙ • V`,
patches `σ` into a global section, which is kept equal to `σ` on `V` itself. Each piece is a
translate of `σ` restricted to a measurable set, so `s` is measurable when `σ` is.

When `V` is open and `σ` is continuous on `V`, this gives a Borel section of `p` that is still
continuous near the identity. Such sections are what the multipliers `s g * s h * (s (g * h))⁻¹`
of projective representations are computed from: they are Borel everywhere and continuous near
`(1, 1)`.

## Main statements

* `MonoidHom.exists_measurable_rightInverse_eqOn`: a measurable section of a surjective
  homomorphism over a measurable neighbourhood `V` of `1` extends to a measurable global section
  agreeing with it on `V`.
* `MonoidHom.exists_measurable_rightInverse_eqOn_of_continuousOn`: a section continuous on an open
  neighbourhood `V` of `1` extends to a Borel global section agreeing with it on `V`.

## References

* K.-H. Neeb, *Abelian extensions of infinite-dimensional Lie groups*, Travaux mathématiques 15
  (2004), Proposition II.6, for extensions with a section continuous near `1` and the
  multipliers they define.
-/

public section

open Function Set Topology

open scoped Pointwise

variable {E G : Type*} [MulOneClass E] [Group G] [TopologicalSpace G]

namespace MonoidHom

/-- **Countable patching of a local section.** Let `p : E →* G` be a surjective homomorphism onto
a Lindelöf group with continuous left translations, and let `σ : G → E` be a measurable map that
is a section of `p` on a measurable neighbourhood `V` of `1`. Then `p` has a measurable section
that agrees with `σ` on `V`. -/
@[to_additive /-- **Countable patching of a local section.** Let `p : E →+ G` be a surjective
homomorphism onto a Lindelöf additive group with continuous translations, and let `σ : G → E` be
a measurable map that is a section of `p` on a measurable neighbourhood `V` of `0`. Then `p` has a
measurable section that agrees with `σ` on `V`. -/]
theorem exists_measurable_rightInverse_eqOn [MeasurableSpace E] [MeasurableMul E]
    [ContinuousConstSMul G G] [LindelofSpace G] [MeasurableSpace G] [MeasurableConstSMul G G]
    (p : E →* G) (hp : Surjective p) {V : Set G} (hV : V ∈ 𝓝 1) (hVm : MeasurableSet V) {σ : G → E}
    (hσ : Measurable σ) (hpσ : ∀ g ∈ V, p (σ g) = g) :
    ∃ s : G → E, Measurable s ∧ RightInverse s p ∧ EqOn s σ V := by
  classical
  -- countably many translates `f n • V` cover `G`
  obtain ⟨t, htc, htV⟩ := countable_cover_nhds (U := fun g : G ↦ g • V) fun g ↦ by
    simpa using smul_mem_nhds_smul g hV
  obtain ⟨f, rfl⟩ := htc.exists_eq_range <| by
    obtain ⟨g, hgt, -⟩ := mem_iUnion₂.1 (htV ▸ mem_univ (1 : G))
    exact ⟨g, hgt⟩
  rw [biUnion_range, iUnion_eq_univ_iff] at htV
  have hmem (n : ℕ) (x : G) : x ∈ f n • V ↔ (f n)⁻¹ * x ∈ V := mem_smul_set_iff_inv_smul_mem
  -- on the first translate containing `x`, use the translate of `σ` by a lift of `f n`
  set patch : ℕ → G → E := fun n x ↦ surjInv hp (f n) * σ ((f n)⁻¹ • x)
  have hpatch : Measurable fun x ↦ patch (Nat.find (htV x)) x :=
    Measurable.find (f := patch) (fun n ↦ (hσ.comp (measurable_const_smul _)).const_mul _)
      (fun n ↦ by simp_rw [hmem]; exact measurable_const_smul (f n)⁻¹ hVm) htV
  refine ⟨V.piecewise σ fun x ↦ patch (Nat.find (htV x)) x, hσ.piecewise hVm hpatch,
    fun x ↦ ?_, fun x hx ↦ piecewise_eq_of_mem _ _ _ hx⟩
  by_cases hx : x ∈ V
  · simp [hx, hpσ]
  · simp [hx, patch, surjInv_eq hp, hpσ _ ((hmem _ _).1 (Nat.find_spec (htV x)))]

/-- **Borel sections from a local continuous section.** Let `p : E →* G` be a surjective
homomorphism onto a Lindelöf group with continuous translations, for instance a second-countable
topological group, and let `σ : G → E` be a section of `p` on an open neighbourhood `V` of `1`
that is continuous on `V`. Then `p` has a Borel section that agrees with `σ` on `V`, so it is
continuous on `V`. -/
@[to_additive /-- **Borel sections from a local continuous section.** Let `p : E →+ G` be a
surjective homomorphism onto a Lindelöf additive group with continuous translations, for instance
a second-countable topological additive group, and let `σ : G → E` be a section of `p` on an open
neighbourhood `V` of `0` that is continuous on `V`. Then `p` has a Borel section that agrees with
`σ` on `V`, so it is continuous on `V`. -/]
theorem exists_measurable_rightInverse_eqOn_of_continuousOn [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableMul E] [SeparatelyContinuousMul G]
    [LindelofSpace G] [MeasurableSpace G] [BorelSpace G] (p : E →* G) (hp : Surjective p)
    {V : Set G} (hVo : IsOpen V) (h1 : 1 ∈ V) {σ : G → E} (hσ : ContinuousOn σ V)
    (hpσ : ∀ g ∈ V, p (σ g) = g) :
    ∃ s : G → E, Measurable s ∧ RightInverse s p ∧ EqOn s σ V := by
  classical
  -- extend `σ` by `1` off `V`, which makes it Borel without changing it on `V`
  obtain ⟨s, hs, hsp, hsσ⟩ := p.exists_measurable_rightInverse_eqOn hp (hVo.mem_nhds h1)
    hVo.measurableSet (hσ.measurable_piecewise continuousOn_const hVo.measurableSet)
    (σ := V.piecewise σ 1) fun g hg ↦ by simp [hg, hpσ]
  exact ⟨s, hs, hsp, fun g hg ↦ (hsσ hg).trans (piecewise_eq_of_mem _ _ _ hg)⟩

end MonoidHom
