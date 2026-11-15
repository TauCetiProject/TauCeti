/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Criterion
public import TauCeti.Topology.Algebra.Group.Profinite.Free.SuccessiveApproximation.Basic

/-!
# Labute's normal form at an odd prime with `q = p`

Let `F = freeProP p (Fin n)` be the free pro-`p` group on `n` generators, with `p` odd, and let
`r ∈ λ_1(F) = Φ(F)` be a relator whose class `ρ ∈ gr_1(F)` has nondegenerate degree-one form and a
nonzero `p`-power part. The normal form modulo `λ_2(F)`
(`TauCeti.freeProP.exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo`) brings `r`
to `x₁^p (x₁, x₂) ⋯ (x_{n-1}, x_n)` modulo `λ_2(F)`; the `p`-power part rules out the alternative
`q = 0`, because `p`-power coordinates transform linearly under a change of basis. For odd `p` and
a class with a `p`-power part whose derivatives span `gr_0(F)`, which is the nondegeneracy of the
form, the basis-modification map `δ_ρ` is onto every `gr_{m+1}(F)`
(`TauCeti.freeProP.range_basisModificationDelta_eq_top_of_odd`), and the successive-approximation
theorem turns the congruence modulo `λ_2(F)` into an equality: a continuous automorphism of `F`
carries `r` to the normal-form word exactly.

For a Demushkin group `G ≅ ⟨x₁, …, x_n ∣ r⟩` at an odd prime whose relator has a `p`-power part,
this is Labute's Theorem 3 in the case `q = p`: `G` is presented by the single relator
`x₁^p (x₁, x₂) ⋯ (x_{n-1}, x_n)`. The `p`-power part of the class of `r` in `gr_1(F)` is nonzero
exactly when the `q`-invariant of the presented group is `p`
(`TauCeti.demushkinQ_presentedProP_eq_iff_exists_degreeOneBasis_repr_inl_ne_zero`). The other
cases of that theorem with `q ≠ 2`, the relators without `p`-power part, where `q ≠ p`, are treated
in `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.NeTwo`, which also states the
theorem for the presented group and intrinsically for a Demushkin group with `q ≠ 2`; the dyadic
relators with `q = 2` are not treated here.

## Main results

* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_odd`: a continuous
  automorphism of `F` carries `r` to `x₁^p (x₁, x₂) ⋯ (x_{n-1}, x_n)`.

## References

* J. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §3,
  Theorem 3.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.5.
-/

public section

namespace TauCeti

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the coordinate
-- hypotheses below are stated over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

namespace freeProP

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **Labute's normal form for odd `p` and `q = p`** (Labute, Theorem 3, the case `q = p`). Let
`F` be the free pro-`p` group on `n` generators with `p` odd, and let `r ∈ λ_1(F)` be a relator
whose class in `gr_1(F)` has nondegenerate degree-one form and a nonzero `p`-power part. Then a
continuous automorphism of `F` carries `r` to `x₁^p (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordNeTwo_of_odd (hp : Odd p)
    (r : pLowerCentralSeries p (freeProP p (Fin n)) 1)
    (hnd : (degreeOneForm (gradedMk p (freeProP p (Fin n)) 1 r)).Nondegenerate)
    (hc : ∃ i, (degreeOneBasis p (Fin n)).repr (gradedMk p (freeProP p (Fin n)) 1 r)
      (Sum.inl i) ≠ 0) :
    ∃ e : freeProP p (Fin n) ≃ₜ* freeProP p (Fin n),
      e r = demushkinWordNeTwo p n (freeProPGen p n) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact absurd hp (by decide)
  obtain ⟨i, hi⟩ := hc
  have hn : 0 < n := i.pos
  set ρ := gradedMk p (freeProP p (Fin n)) 1 r with hρ
  obtain ⟨-, e₁, he₁⟩ := exists_continuousMulEquiv_gradedMap_eq_gradedMk_demushkinWordNeTwo ρ hnd
    (isAlt_degreeOneForm_of_ne_two hp2 ρ)
  set f : freeProP p (Fin n) →ₜ* freeProP p (Fin n) :=
    (e₁ : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
  set w : pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    ⟨demushkinWordNeTwo p n (freeProPGen p n),
      demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _⟩ with hw
  -- `e₁ r ∈ λ_1(F)` has class `(e₁)_* ρ`.
  have hmem : f r ∈ pLowerCentralSeries p (freeProP p (Fin n)) 1 :=
    f.toMonoidHom.map_pLowerCentralSeries_le f.continuous 1 ⟨r, r.2, rfl⟩
  have hr' : gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩ =
      gradedMap p f.toMonoidHom f.continuous 1 ρ := by
    rw [hρ, gradedMap_gradedMk]
    rfl
  -- The alternative `q = 0` is excluded: a class without `p`-power part keeps none under
  -- `(e₁⁻¹)_*`, while `ρ` has one.
  have hclass : gradedMap p f.toMonoidHom f.continuous 1 ρ =
      gradedMk p (freeProP p (Fin n)) 1 w := by
    rcases he₁ with he₁ | he₁
    · exfalso
      apply hi
      set f' : freeProP p (Fin n) →ₜ* freeProP p (Fin n) :=
        (e₁.symm : freeProP p (Fin n) →ₜ* freeProP p (Fin n))
      have hback : gradedMap p f'.toMonoidHom f'.continuous 1
          (gradedMap p f.toMonoidHom f.continuous 1 ρ) = ρ := by
        obtain ⟨x, hx⟩ := gradedMk_surjective 1 ρ
        rw [← hx, gradedMap_gradedMk, gradedMap_gradedMk]
        congr 1
        exact Subtype.ext (e₁.symm_apply_apply x)
      rw [← hback, degreeOneBasis_repr_gradedMap_inl, he₁]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      rw [degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl (dvd_zero p)]
      simp
    · exact he₁
  -- The span hypothesis for the class of `e₁ r`, which is the class of the normal-form word.
  have hspan : ∀ m (hm : 1 ≤ m), LinearMap.range (basisModificationDelta p (Fin n) hm
      (gradedMk p (freeProP p (Fin n)) 1 ⟨f r, hmem⟩)) = ⊤ := by
    intro m hm
    refine range_basisModificationDelta_eq_top_of_odd hp hm ?_ ⟨⟨0, hn⟩, ?_⟩
    · rw [span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm, hr']
      exact (nondegenerate_degreeOneForm_gradedMap_iff e₁ ρ).2 hnd
    · rw [hr', hclass, hw, degreeOneBasis_repr_gradedMk_demushkinWordNeTwo_inl dvd_rfl]
      simp [Nat.div_self (Fact.out : p.Prime).pos]
  obtain ⟨e₂, he₂⟩ :=
    exists_continuousMulEquiv_apply_eq_of_range_basisModificationDelta_eq_top
      ⟨f r, hmem⟩ w (hr'.trans hclass) hspan
  exact ⟨e₁.trans e₂, he₂⟩

end freeProP

end TauCeti
