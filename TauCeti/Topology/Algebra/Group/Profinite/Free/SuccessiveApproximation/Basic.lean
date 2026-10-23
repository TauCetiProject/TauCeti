/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Comparison
import TauCeti.Algebra.Group.Subgroup.Congruence

/-!
# Successive approximation of a relator by basis modifications

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with lower
`p`-series `λ_k = λ_k(F)`, and let `r, w ∈ λ_1(F)` be two relators with the same class
`ρ ∈ gr_1(F)`, that is `r ≡ w mod λ_2(F)`. The basis modification `θ_w : x_i ↦ x_i * w_i` by a
family `w : X → λ_m(F)` moves `r` inside its coset modulo `λ_{m+1}(F)` by the class
`δ_ρ(ω) ∈ gr_{m+1}(F)` of `TauCeti.freeProP.basisModificationDelta`, and it leaves the class `ρ`
unchanged. So a congruence `r ≡ w mod λ_{m+1}` improves to a congruence modulo `λ_{m+2}` by one
basis modification at level `m` as soon as the class of the deviation `r⁻¹ * w` in `gr_{m+1}(F)`
lies in the image of `δ_ρ` (`TauCeti.freeProP.inv_basisModification_mul_mem_pLowerCentralSeries`),
and finitely many modifications carry `r` to `w` modulo any term of the series.

The limit is taken by
`TauCeti.IsProP.exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective` of
`TauCeti.Topology.Algebra.Group.Profinite.ProP.Comparison`, which holds in any topologically
finitely generated pro-`p` group: the finite approximations are surjective endomorphisms of `F` by
Burnside's criterion (`TauCeti.IsProP.surjective_of_forall_inv_mul_mem_pLowerCentralSeries_one`),
and the levelwise comparison schema assembles them into a continuous automorphism `e` of `F` with
`e r = w`. Constraints `x_i⁻¹ * φ(x_i) ∈ C i` on the approximations by closed subgroups `C i` pass
to `e`, since membership in a closed subgroup is detected on the finite quotients of `F`.

## The constrained argument

The map `δ_ρ` is rarely onto `gr_{m+1}(F)`, and the corrections that a normal-form argument may use
are often restricted: they have to lie in the kernel of a character, or in the closed commutator
subgroup, so that an invariant of the moving relator is preserved. The successive-approximation
theorem is therefore stated with two constraints, a set `Z ⊆ F` in which the deviations are known to
lie and a family `C : X → Subgroup F` of **admissible corrections**, one subgroup per generator. A
continuous endomorphism `φ` of `F` is *admissible* when `x_i⁻¹ * φ(x_i) ∈ C i` for every `i`; the
basis modification `θ_ω` by a family with `ω_i ∈ C i` is admissible, and a composite `θ_ω ∘ φ` of
an admissible basis modification with an admissible `φ` is admissible as soon as `θ_ω` maps each
`C i` into itself. The hypotheses of the theorem are then

* **stability:** every admissible basis modification `θ_ω`, `ω : X → λ_1(F)`, preserves each `C i`;
* **the invariant:** for every admissible `φ` congruent to the identity modulo `λ_1(F)` the
  deviation `(φ r)⁻¹ * w` lies in `Z`;
* **the constrained span statement:** for every `m ≥ 1`, the class in `gr_{m+1}(F)` of an element
  of `λ_{m+1}(F) ∩ Z` is `δ_ρ(⟦ω⟧)` for a family `ω : X → λ_m(F)` with `ω_i ∈ C i` for every `i`.

Under them every finite approximation is admissible
(`TauCeti.freeProP.exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries`), and when
each `C i` is closed an admissible continuous automorphism of `F` carries `r` to `w`
(`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq`).
The constrained span statement is assumed, not established here; span statements for `δ_ρ`, such as
those of `TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification`, supply it for the
relators in normal form.

Two special cases are the successive-approximation theorems of Labute's proof of his normal-form
theorem.

* When `δ_ρ` is onto `gr_{m+1}(F)` for every `m ≥ 1`, every deviation is absorbed with no
  constraint, `Z = F` and `C i = F`
  (`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`).
  This hypothesis is established for the relators `x₁^p (x₁, x₂) (x₃, x₄) ⋯` at odd `p`
  (`TauCeti.freeProP.range_basisModificationDelta_eq_top_of_odd`).
* When `ρ` has no `p`-power part, `Im δ_ρ` misses the classes `π^{m+1} ξ_i` of the `p`-powers of
  the generators, so `δ_ρ` is not onto `gr_{m+1}(F)`. The **relative** theorem
  (`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_exponentSum_eq`) takes `Z` to be the
  closed commutator subgroup `K = closure [F, F]` and `C i = K` at the generators `i` carrying a
  nonzero coordinate of the exponent vector `v = exponentSum r`, with no constraint elsewhere: it
  assumes that `r` and `w` have the same exponent vector, and that every deviation in
  `λ_{m+1}(F) ∩ K` is `δ_ρ` of a level-`m` correction `ω` with `ω_i ∈ K` at every `i` with
  `v_i ≠ 0`. Such a correction preserves the exponent vector of the relator
  (`TauCeti.freeProP.exponentSum_apply_eq_of_forall_inv_mul_apply_mem`), which is the invariant
  keeping the deviation in `K` at every level. The relators `x₁^q (x₁, x₂) (x₃, x₄) ⋯` with `q = 0`
  or `q = p^f`, `f ≥ 2`, whose `p`-power part `x₁^q` lies in `λ_2(F)`, are the intended
  application; for `q = 0` the relator lies in `K`, the exponent vector vanishes and the constraint
  on `ω` is empty.

The general form is the shape of Labute's arguments over the kernel `X = ker χ` of an orientation
character `χ` of `F`: there `C i = X` for every `i`, so that the admissible modifications, and the
automorphism of the conclusion, preserve `χ`, and `Z` is the set of elements of `X` killed by a
family of continuous crossed homomorphisms
`F → ℤ_p` twisted by `χ`, an invariant of the relator that the admissible modifications of a
normal-form word also preserve.

## Main results

* `TauCeti.freeProP.inv_basisModification_mul_mem_pLowerCentralSeries`: one step of the
  approximation, a basis modification absorbing the class of the deviation.
* `TauCeti.freeProP.exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries`: the
  finite approximations, one admissible basis modification per level.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq` is **the constrained
  successive-approximation theorem**: an admissible continuous automorphism of `F` carries `r` to
  `w` when the deviations in `Z` are absorbed by admissible corrections and the `C i` are closed.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`:
  the unconstrained case, where `δ_ρ` is onto in every degree.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_exponentSum_eq` is **the relative
  successive-approximation theorem**: the case of two relators with the same exponent vector, whose
  deviations in the closed commutator subgroup are absorbed by corrections preserving that vector.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3, and §4, the proofs of Theorems 5 and 6.
-/

public section

namespace TauCeti.freeProP

open Subgroup

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Finite X] [LinearOrder X]

/-! ### One step of the approximation -/

/-- **One step of the successive approximation.** Let `s ∈ λ_1(F)` and `w ∈ F` with
`s⁻¹ * w ∈ λ_{m+1}(F)`, `m ≥ 1`, and let `ω : X → λ_m(F)` be a family whose classes satisfy
`δ_σ(⟦ω⟧) = ` the class of `s⁻¹ * w` in `gr_{m+1}(F)`, where `σ ∈ gr_1(F)` is the class of `s`. Then
the basis modification `θ_ω` improves the congruence by one level: `(θ_ω s)⁻¹ * w ∈ λ_{m+2}(F)`. -/
theorem inv_basisModification_mul_mem_pLowerCentralSeries {m : ℕ} (hm : 1 ≤ m)
    (s : pLowerCentralSeries p (freeProP p X) 1) (w : freeProP p X)
    (hs : (s : freeProP p X)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (m + 1))
    (ω : X → pLowerCentralSeries p (freeProP p X) m)
    (hω : basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 s)
        (fun i ↦ gradedMk p (freeProP p X) m (ω i)) =
      gradedMk p (freeProP p X) (m + 1) ⟨(s : freeProP p X)⁻¹ * w, hs⟩) :
    (basisModification ω s)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (m + 2) := by
  have key := gradedMk_inv_mul_basisModification hm ω s
  rw [hω] at key
  have h : ((s : freeProP p X)⁻¹ * basisModification ω s)⁻¹ * ((s : freeProP p X)⁻¹ * w) ∈
      pLowerCentralSeries p (freeProP p X) (m + 2) :=
    QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp key)
  rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at h

/-! ### The finite approximations -/

/-- **Finite successive approximation with constraints.** Let `r, w ∈ λ_1(F)` have the same class
`ρ ∈ gr_1(F)`, let `Z ⊆ F` and let `C : X → Subgroup F` be the admissible corrections, with every
admissible basis modification `θ_ω`, `ω : X → λ_1(F)` with `ω_i ∈ C i` for every `i`, preserving
each `C i`, and every admissible endomorphism `φ` of `F`, one with `x_i⁻¹ * φ(x_i) ∈ C i` for every
`i`, congruent to the identity modulo `λ_1(F)` having its deviation `(φ r)⁻¹ * w` in `Z`. Suppose
that for `1 ≤ m ≤ k` every element of `λ_{m+1}(F)` lying in `Z` has class `δ_ρ(⟦ω⟧)` for a family
`ω : X → λ_m(F)` with `ω_i ∈ C i` for every `i`. Then there is an admissible continuous
endomorphism `φ` of `F`, congruent to the identity modulo `λ_1(F)`, with `φ r ≡ w mod λ_{k+2}(F)`.
-/
theorem exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries
    (Z : Set (freeProP p X)) (C : X → Subgroup (freeProP p X))
    (hC : ∀ ω : X → pLowerCentralSeries p (freeProP p X) 1, (∀ i, (ω i : freeProP p X) ∈ C i) →
      ∀ i, ∀ c ∈ C i, basisModification ω c ∈ C i)
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hZ : ∀ φ : freeProP p X →ₜ* freeProP p X,
      (∀ g, g⁻¹ * φ g ∈ pLowerCentralSeries p (freeProP p X) 1) →
      (∀ i, (of i)⁻¹ * φ (of i) ∈ C i) → (φ r)⁻¹ * w ∈ Z)
    (k : ℕ)
    (hspan : ∀ m (hm : 1 ≤ m), m ≤ k → ∀ z : pLowerCentralSeries p (freeProP p X) (m + 1),
      (z : freeProP p X) ∈ Z →
      ∃ ω : X → pLowerCentralSeries p (freeProP p X) m, (∀ i, (ω i : freeProP p X) ∈ C i) ∧
        basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
          (fun i ↦ gradedMk p (freeProP p X) m (ω i)) = gradedMk p (freeProP p X) (m + 1) z) :
    ∃ φ : freeProP p X →ₜ* freeProP p X,
      (∀ g, g⁻¹ * φ g ∈ pLowerCentralSeries p (freeProP p X) 1) ∧
        (∀ i, (of i)⁻¹ * φ (of i) ∈ C i) ∧
        (φ r)⁻¹ * w ∈ pLowerCentralSeries p (freeProP p X) (k + 2) := by
  induction k with
  | zero =>
    refine ⟨ContinuousMonoidHom.id _, fun g ↦ ?_, fun i ↦ ?_, ?_⟩
    · simp
    · simp
    · simpa using QuotientGroup.eq.mp (gradedMk_eq_gradedMk_iff.mp h)
  | succ k ih =>
    obtain ⟨φ, hφ, hφC, hr⟩ := ih fun m hm hmk ↦ hspan m hm (hmk.trans k.le_succ)
    -- `φ r` is again a relator with class `ρ`: `φ` is congruent to the identity modulo `λ_2` on
    -- `λ_1`.
    have hφr : φ r ∈ pLowerCentralSeries p (freeProP p X) 1 :=
      φ.toMonoidHom.map_pLowerCentralSeries_le φ.continuous 1 ⟨r, r.2, rfl⟩
    have hρ : gradedMk p (freeProP p X) 1 ⟨φ r, hφr⟩ = gradedMk p (freeProP p X) 1 r := by
      rw [gradedMk_eq_gradedMk_iff]
      exact (QuotientGroup.eq.mpr
        (inv_mul_apply_mem_pLowerCentralSeries φ.toMonoidHom φ.continuous hφ r.2)).symm
    -- The deviation `(φ r)⁻¹ * w` lies in `Z`, because `φ` is admissible; the constrained span
    -- statement absorbs it by an admissible correction.
    obtain ⟨ω, hωC, hω⟩ := hspan (k + 1) (by omega) le_rfl ⟨(φ r)⁻¹ * w, hr⟩ (hZ φ hφ hφC)
    -- The correction `ω`, read as a family in `λ_1(F)`: the stability hypothesis applies to it.
    let ω₁ : X → pLowerCentralSeries p (freeProP p X) 1 := fun i ↦
      ⟨ω i, pLowerCentralSeries_antitone (by omega) (ω i).2⟩
    have hω₁ : basisModification ω₁ = basisModification ω :=
      hom_ext fun i ↦ by rw [basisModification_of, basisModification_of]
    refine ⟨(basisModification ω).comp φ, fun g ↦ ?_, fun i ↦ ?_, ?_⟩
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply]
      exact inv_mul_apply_apply_mem (fun g ↦ pLowerCentralSeries_antitone (by omega)
        (inv_mul_basisModification_mem_pLowerCentralSeries ω g)) hφ g
    · -- `θ_ω (φ x_i) = x_i * ω_i * θ_ω (x_i⁻¹ * φ x_i)`, and both factors lie in `C i`.
      rw [ContinuousMonoidHom.coe_comp, Function.comp_apply,
        ← mul_inv_cancel_left (of i) (φ (of i)), map_mul, basisModification_of, mul_assoc,
        inv_mul_cancel_left, ← hω₁]
      exact mul_mem (hωC i) (hC ω₁ hωC i _ (hφC i))
    · rw [ContinuousMonoidHom.coe_comp, Function.comp_apply]
      refine inv_basisModification_mul_mem_pLowerCentralSeries le_add_self ⟨φ r, hφr⟩ w hr ω ?_
      rw [hρ]
      exact hω

/-! ### The limit -/

/-- **The constrained successive-approximation theorem.** Let `r, w ∈ λ_1(F)` be relators of the
free pro-`p` group `F` on a finite linearly ordered type with the same class `ρ ∈ gr_1(F)`, let
`Z ⊆ F` and let `C : X → Subgroup F` be closed admissible corrections, with every admissible basis
modification `θ_ω`, `ω : X → λ_1(F)` with `ω_i ∈ C i` for every `i`, preserving each `C i`, and
every admissible endomorphism `φ` of `F`, one with `x_i⁻¹ * φ(x_i) ∈ C i` for every `i`, congruent
to the identity modulo `λ_1(F)` having its deviation `(φ r)⁻¹ * w` in `Z`. Suppose that for every
`m ≥ 1` each element of `λ_{m+1}(F)` lying in `Z` has class `δ_ρ(⟦ω⟧)` for a family
`ω : X → λ_m(F)` with `ω_i ∈ C i` for every `i`. Then an admissible continuous automorphism of `F`
carries `r` to `w`.

The admissibility of the automorphism is the limit of the admissibility of the finite
approximations, which needs the `C i` closed. The constrained span statement is the hypothesis a
normal-form argument has to establish; it is assumed here. Taking `Z = F` and `C i = F` recovers
the unconstrained theorem
`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top`. -/
theorem exists_continuousMulEquiv_apply_eq
    (Z : Set (freeProP p X)) (C : X → Subgroup (freeProP p X))
    (hclosed : ∀ i, IsClosed (C i : Set (freeProP p X)))
    (hC : ∀ ω : X → pLowerCentralSeries p (freeProP p X) 1, (∀ i, (ω i : freeProP p X) ∈ C i) →
      ∀ i, ∀ c ∈ C i, basisModification ω c ∈ C i)
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hZ : ∀ φ : freeProP p X →ₜ* freeProP p X,
      (∀ g, g⁻¹ * φ g ∈ pLowerCentralSeries p (freeProP p X) 1) →
      (∀ i, (of i)⁻¹ * φ (of i) ∈ C i) → (φ r)⁻¹ * w ∈ Z)
    (hspan : ∀ m (hm : 1 ≤ m), ∀ z : pLowerCentralSeries p (freeProP p X) (m + 1),
      (z : freeProP p X) ∈ Z →
      ∃ ω : X → pLowerCentralSeries p (freeProP p X) m, (∀ i, (ω i : freeProP p X) ∈ C i) ∧
        basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
          (fun i ↦ gradedMk p (freeProP p X) m (ω i)) = gradedMk p (freeProP p X) (m + 1) z) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, (∀ i, (of i)⁻¹ * e (of i) ∈ C i) ∧ e r = w := by
  refine (isProP_freeProP p X).exists_continuousMulEquiv_apply_eq_of_forall_exists_surjective
    (isTopologicallyFinitelyGenerated_freeProP p X) Fact.out (r : freeProP p X) w of C hclosed
    fun k ↦ ?_
  obtain ⟨φ, hφ, hφC, hr⟩ := exists_continuousMonoidHom_inv_mul_apply_mem_pLowerCentralSeries Z C
    hC r w h hZ k fun m hm _ ↦ hspan m hm
  exact ⟨φ, (isProP_freeProP p X).surjective_of_forall_inv_mul_mem_pLowerCentralSeries_one
    (φ := φ.toMonoidHom) φ.continuous hφ, hφC, pLowerCentralSeries_antitone (by omega) hr⟩

/-- **The unconstrained successive-approximation theorem.** Let `r, w ∈ λ_1(F)` be relators of
the free pro-`p` group `F` on a finite linearly ordered type with the same class `ρ ∈ gr_1(F)`, and
suppose the basis-modification map `δ_ρ` is onto `gr_{m+1}(F)` for every `m ≥ 1`. Then a continuous
automorphism of `F` carries `r` to `w`. -/
theorem exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hspan : ∀ m (hm : 1 ≤ m),
      LinearMap.range (basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)) = ⊤) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, e r = w := by
  refine (exists_continuousMulEquiv_apply_eq Set.univ (fun _ ↦ ⊤) (fun _ ↦ isClosed_univ)
    (fun _ _ _ _ _ ↦ mem_top _) r w h (fun _ _ _ ↦ Set.mem_univ _) fun m hm z _ ↦ ?_).imp
    fun _ ↦ And.right
  -- The class of `z` is `δ_ρ(v)` for some `v`; lift the `v_i` to `ω_i ∈ λ_m(F)`.
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.mp (hspan m hm) (gradedMk p (freeProP p X) (m + 1) z)
  choose ω hω using fun i ↦ gradedMk_surjective m (v i)
  exact ⟨ω, fun _ ↦ mem_top _, by rw [funext hω, hv]⟩

/-- **The relative successive-approximation theorem.** Let `r, w ∈ λ_1(F)` be relators of the
free pro-`p` group `F` on a finite linearly ordered type with the same class `ρ ∈ gr_1(F)` and the
same exponent vector `v = exponentSum r`, and suppose that for every `m ≥ 1` each element of
`λ_{m+1}(F)` lying in the closed commutator subgroup `K` has class `δ_ρ(⟦ω⟧)` for a family
`ω : X → λ_m(F)` with `ω_i ∈ K` at every generator `i` with `v_i ≠ 0`. Then a continuous
automorphism of `F` carries `r` to `w`.

This is the form of the argument for a relator whose `p`-power part lies in `λ_2(F)`: there `Im δ_ρ`
misses the classes `π^{m+1} ξ_i`, so `δ_ρ` is not onto. It is the constrained theorem
`TauCeti.freeProP.exists_continuousMulEquiv_apply_eq` with `Z = K` and with `C i = K` at the
generators carrying a nonzero exponent: such corrections preserve the exponent vector of the
relator, which keeps the deviations in `K` along the approximation. The hypothesis on the
corrections is the constrained form of the span statement that `Im δ_ρ` contains the class of
every element of `λ_{m+1}(F) ∩ K`; it is assumed here, not established. -/
theorem exists_continuousMulEquiv_apply_eq_of_exponentSum_eq
    (r w : pLowerCentralSeries p (freeProP p X) 1)
    (h : gradedMk p (freeProP p X) 1 r = gradedMk p (freeProP p X) 1 w)
    (hrw : exponentSum p X r = exponentSum p X w)
    (hspan : ∀ m (hm : 1 ≤ m), ∀ z : pLowerCentralSeries p (freeProP p X) (m + 1),
      (z : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure →
      ∃ ω : X → pLowerCentralSeries p (freeProP p X) m,
        (∀ i, (exponentSum p X r).toAdd i ≠ 0 →
          (ω i : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure) ∧
        basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
          (fun i ↦ gradedMk p (freeProP p X) m (ω i)) = gradedMk p (freeProP p X) (m + 1) z) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, e r = w := by
  classical
  -- The admissible corrections: the closed commutator subgroup at the generators carrying a
  -- nonzero exponent, everything elsewhere.
  refine (exists_continuousMulEquiv_apply_eq
    ((commutator (freeProP p X)).topologicalClosure : Set _)
    (fun i ↦ if (exponentSum p X r).toAdd i ≠ 0 then (commutator (freeProP p X)).topologicalClosure
      else ⊤) (fun i ↦ ?_) (fun ω _ i c hc ↦ ?_) r w h (fun φ _ hφ ↦ ?_)
    fun m hm z hz ↦ ?_).imp fun _ ↦ And.right
  · split_ifs
    · exact isClosed_topologicalClosure _
    · exact isClosed_univ
  · -- Every continuous endomorphism maps the closed commutator subgroup into itself.
    split_ifs at hc ⊢ with hi
    · exact TopologicalAbelianization.topologicalClosure_commutator_le_comap
        (basisModification ω).toMonoidHom (basisModification ω).continuous hc
    · exact mem_top _
  · -- An admissible endomorphism preserves the exponent vector of `r`, so its deviation from `w`
    -- has trivial exponent vector.
    rw [SetLike.mem_coe, ← exponentSum_eq_one_iff, map_mul, map_inv, ← hrw,
      exponentSum_apply_eq_of_forall_inv_mul_apply_mem φ fun i hi ↦ by simpa [hi] using hφ i,
      inv_mul_cancel]
  · obtain ⟨ω, hωK, hω⟩ := hspan m hm z hz
    refine ⟨ω, fun i ↦ ?_, hω⟩
    split_ifs with hi
    · exact hωK i hi
    · exact mem_top _

end TauCeti.freeProP
