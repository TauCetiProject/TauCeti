/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Orientation
public import TauCeti.Geometry.Symplectic.Darboux.Basis
public import TauCeti.Geometry.Symplectic.Rescale
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.LinearAlgebra.Orientation.Prod

import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import TauCeti.LinearAlgebra.Basis.Triangular
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# The symplectic orientation

Let `ω` be a symplectic form on a finite-dimensional real vector space `V`. Any two Darboux bases
(`TauCeti.SymplecticForm.IsDarbouxBasis`, in `TauCeti.Geometry.Symplectic.Darboux.Basis`) have
relative determinant `1` (`TauCeti.SymplecticForm.IsDarbouxBasis.det_eq_one`).

All Darboux bases, listed in the interleaved order `(q₁, p₁, q₂, p₂, …, qₙ, pₙ)` (the reindexing
by `finProdFinEquiv`), therefore induce one orientation of `V`: the **symplectic orientation**
`TauCeti.SymplecticForm.orientation` (`TauCeti.SymplecticForm.IsDarbouxBasis.orientation_reindex`).
Classically it is described as the orientation in which the top form `ωⁿ`, which takes the
value `n!` on `(q₁, p₁, …, qₙ, pₙ)`, is positive; this file characterizes it through Darboux
bases only and does not use exterior powers of `ω`.

The symplectic orientation is natural: a linear symplectomorphism carries the symplectic
orientation of its source to that of its target
(`TauCeti.SymplecticForm.IsSymplectomorphism.map_orientation`). Rescaling `ω` by `c ≠ 0` changes
it by the sign of `cⁿ` (`TauCeti.SymplecticForm.orientation_rescale`), so positive rescaling
preserves it, while `-ω` has the opposite orientation exactly when `n` is odd. The symplectic
orientation of a direct sum `ω₁ ⊕ ω₂` is the product of the symplectic orientations of the
summands (`TauCeti.SymplecticForm.orientation_prod`). On the plane `ℝ × ℝ`, the standard
symplectic form `ds ∧ dt` induces the orientation of the standard basis `(∂_s, ∂_t)`
(`TauCeti.SymplecticForm.orientation_stdSymplecticForm_real`).

The symplectic orientation is also determined by any almost complex structure `J` that `ω` tames,
`ω(v, J v) > 0` for `v ≠ 0`: every `J`-adapted basis `(v₁, J v₁, …, vₙ, J vₙ)` is positive
(`TauCeti.SymplecticForm.Tames.orientation_reindex`). The proof is the symplectic Gram–Schmidt
process: the span of the first `i` adapted pairs is `J`-invariant, hence symplectic, and projecting
the next pair onto its symplectic complement yields a Darboux basis whose matrix in the adapted
basis is triangular with positive diagonal. Hence two symplectic forms taming a common `J` have the
same orientation (`TauCeti.SymplecticForm.Tames.orientation_eq`). Taming a fixed `J` is an open
condition on `ω`, so this is the input for the local constancy of the tangent symplectic
orientations of a symplectic manifold.

This is the linear model for the orientation of a symplectic manifold, read on each tangent
space, and the product law computes the orientation of a product such as
`(ℝ², ds ∧ dt) × (V, ω)`.

## Main definitions

* `TauCeti.SymplecticForm.orientation ω hk`: the symplectic orientation of `V`, indexed by
  `Fin k` where `finrank ℝ V = k`.

## Main results

* `TauCeti.SymplecticForm.orientation_prod`: the symplectic orientation of a direct sum is the
  product of the symplectic orientations.
* `TauCeti.SymplecticForm.orientation_stdSymplecticForm_real`: the standard symplectic form on
  `ℝ × ℝ` induces the orientation of the standard basis.
* `TauCeti.SymplecticForm.orientation_transport_prodAssoc_stdSymplecticForm_prod`: the symplectic
  orientation of `ds ∧ dt + ω` on `ℝ × (ℝ × V)` is `∂_s`, then `∂_t`, then that of `ω`.
* `TauCeti.SymplecticForm.Tames.orientation_reindex`: if `ω` tames `J`, every `J`-adapted basis is
  positive for the symplectic orientation.
* `TauCeti.SymplecticForm.Tames.orientation_eq`: symplectic forms taming a common almost complex
  structure have the same symplectic orientation.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (the symplectic volume form `ωⁿ`).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 1.1 and Homework 1.
-/

public section

open Module

namespace TauCeti

namespace SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {ω : SymplecticForm V} {n : ℕ} {b : Basis (Fin n × Fin 2) ℝ V}

/-! ### The symplectic orientation -/

/-- A symplectic vector space has even dimension `k`, so `k / 2 * 2 = k`. -/
private theorem div_two_mul_two [FiniteDimensional ℝ V] (ω : SymplecticForm V) {k : ℕ}
    (hk : finrank ℝ V = k) : k / 2 * 2 = k :=
  Nat.div_two_mul_two_of_even (hk ▸ ω.isAlt.even_finrank ω.nondegenerate)

variable [FiniteDimensional ℝ V] {k : ℕ}

/-- The **symplectic orientation** of a finite-dimensional symplectic vector space `(V, ω)` with
`finrank ℝ V = k`: the orientation of the Darboux bases `(q₁, p₁, …, qₙ, pₙ)`, listed in this
interleaved order (`TauCeti.SymplecticForm.IsDarbouxBasis.orientation_reindex`). -/
noncomputable def orientation (ω : SymplecticForm V) (hk : finrank ℝ V = k) :
    Orientation ℝ V (Fin k) :=
  ((ω.exists_isDarbouxBasis_of_finrank_eq (hk.trans (ω.div_two_mul_two hk).symm)).choose.reindex
    (finProdFinEquiv.trans (finCongr (ω.div_two_mul_two hk)))).orientation

/-- **Every Darboux basis is positively oriented** for the symplectic orientation: the basis
`(q₁, p₁, …, qₙ, pₙ)`, listed in this interleaved order, induces `ω.orientation`. -/
theorem IsDarbouxBasis.orientation_reindex (hb : ω.IsDarbouxBasis b) (hk : finrank ℝ V = k)
    (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation = ω.orientation hk := by
  obtain rfl : n = k / 2 := by omega
  have hb₀ :=
    (ω.exists_isDarbouxBasis_of_finrank_eq (hk.trans (ω.div_two_mul_two hk).symm)).choose_spec
  rw [orientation, Basis.orientation_reindex, Basis.orientation_reindex,
    (Basis.orientation_eq_iff_det_pos _ _).2 (by rw [hb.det_eq_one hb₀]; exact one_pos)]

/-- The symplectic orientation is natural: a linear symplectomorphism `e : (V, ω₁) → (W, ω₂)`
carries the symplectic orientation of `ω₁` to that of `ω₂`. -/
theorem IsSymplectomorphism.map_orientation [FiniteDimensional ℝ W] {ω₁ : SymplecticForm V}
    {ω₂ : SymplecticForm W} {e : V ≃ₗ[ℝ] W} (he : IsSymplectomorphism ω₁ ω₂ e)
    (hk : finrank ℝ V = k) :
    Orientation.map (Fin k) e (ω₁.orientation hk) =
      ω₂.orientation (e.finrank_eq.symm.trans hk) := by
  have h := ω₁.div_two_mul_two hk
  obtain ⟨b, hb⟩ := ω₁.exists_isDarbouxBasis_of_finrank_eq (hk.trans h.symm)
  rw [← hb.orientation_reindex hk h, ← Basis.orientation_map,
    ← (hb.map he).orientation_reindex _ h]
  exact congrArg Basis.orientation <| Basis.eq_of_apply_eq fun x ↦ by
    simp only [Basis.map_apply, Basis.reindex_apply]

/-- **Rescaling the symplectic orientation.** For `c ≠ 0` and `finrank ℝ V = k`, the symplectic
orientation of `c • ω` is that of `ω` acted on by the unit `c ^ (k / 2)`, that is, by the sign of
`c ^ (k / 2)`. -/
theorem orientation_rescale (ω : SymplecticForm V) {c : ℝ} (hc : c ≠ 0) (hk : finrank ℝ V = k) :
    (ω.rescale c hc).orientation hk = Units.mk0 c hc ^ (k / 2) • ω.orientation hk := by
  have h := ω.div_two_mul_two hk
  obtain ⟨b, hb⟩ := ω.exists_isDarbouxBasis_of_finrank_eq (hk.trans h.symm)
  set u := Units.mk0 c hc
  -- Rescale the momenta `pᵢ` by `c⁻¹`; the result is a Darboux basis of `c • ω`.
  let w : Fin (k / 2) × Fin 2 → ℝˣ := fun p ↦ if p.2 = 0 then 1 else u⁻¹
  have hbw : (ω.rescale c hc).IsDarbouxBasis (b.unitsSMul w) := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simp [w, Basis.unitsSMul_apply, hb.apply_fst_fst]
    · simp [w, Basis.unitsSMul_apply, Units.smul_def, hb.apply_snd_snd]
    · simp [w, u, Basis.unitsSMul_apply, Units.smul_def, hb.apply_fst_snd, hc]
  set E := finProdFinEquiv.trans (finCongr h)
  have hE : (b.unitsSMul w).reindex E = (b.reindex E).unitsSMul (w ∘ E.symm) :=
    Basis.eq_of_apply_eq fun x ↦ by
      simp only [Basis.reindex_apply, Basis.unitsSMul_apply, Function.comp_apply]
  have hw : ∏ x, (w ∘ E.symm) x = u⁻¹ ^ (k / 2) := by
    rw [Fintype.prod_equiv E.symm (w ∘ E.symm) w fun _ ↦ rfl]
    simp [w, Fintype.prod_prod_type, Fin.prod_univ_two]
  rw [← hb.orientation_reindex hk h, ← hbw.orientation_reindex hk h, hE,
    Basis.orientation_unitsSMul, hw, inv_pow, inv_inv]

/-- Positive rescaling preserves the symplectic orientation. -/
theorem orientation_rescale_of_pos (ω : SymplecticForm V) {c : ℝ} (hc : 0 < c)
    (hk : finrank ℝ V = k) : (ω.rescale c hc.ne').orientation hk = ω.orientation hk := by
  rw [orientation_rescale, Module.Ray.units_smul_of_pos]
  simpa using pow_pos hc _

/-- **The symplectic orientation of a direct sum** `ω₁ ⊕ ω₂` is the product of the symplectic
orientations of `ω₁` and `ω₂`. -/
theorem orientation_prod [FiniteDimensional ℝ W] (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W)
    {m k : ℕ} (hm : finrank ℝ V = m) (hk : finrank ℝ W = k) (hmk : finrank ℝ (V × W) = m + k) :
    (ω₁.prod ω₂).orientation hmk =
      Orientation.prod (ω₁.orientation hm) (ω₂.orientation hk) hm hk := by
  have h₁ := ω₁.div_two_mul_two hm
  have h₂ := ω₂.div_two_mul_two hk
  have h : (m / 2 + k / 2) * 2 = m + k := by rw [add_mul, h₁, h₂]
  obtain ⟨b, hb⟩ := ω₁.exists_isDarbouxBasis_of_finrank_eq (hm.trans h₁.symm)
  obtain ⟨c, hc⟩ := ω₂.exists_isDarbouxBasis_of_finrank_eq (hk.trans h₂.symm)
  rw [← hb.orientation_reindex hm h₁, ← hc.orientation_reindex hk h₂,
    Orientation.prod_basis_orientation, ← (hb.prod hc).orientation_reindex hmk h]
  congr 1
  -- Both bases list `(q₁, p₁, …)` of `ω₁` followed by `(q'₁, p'₁, …)` of `ω₂`.
  set e : (Fin (m / 2) × Fin 2) ⊕ (Fin (k / 2) × Fin 2) ≃ Fin (m / 2 + k / 2) × Fin 2 :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  set F := (Equiv.sumCongr (finProdFinEquiv.trans (finCongr h₁))
    (finProdFinEquiv.trans (finCongr h₂))).trans finSumFinEquiv
  have hF (p) : F p = finProdFinEquiv.trans (finCongr h) (e p) := by
    rcases p with ⟨i, a⟩ | ⟨i, a⟩
    · ext
      simp [F, e]
    · ext
      simp [F, e]
      omega
  refine Basis.eq_of_apply_eq fun x ↦ ?_
  obtain ⟨p, rfl⟩ := F.surjective x
  conv_lhs => rw [Basis.reindex_apply, Basis.reindex_apply, hF, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases p with p | p <;> simp [F, Basis.reindex_apply, Basis.prod_apply]

/-- The symplectic orientations of `ω` indexed by `Fin k` and by `Fin k'`, for `k = k'`, correspond
under the identification `finCongr` of the index types. -/
@[simp]
theorem reindex_orientation (ω : SymplecticForm V) {k' : ℕ} (hk : finrank ℝ V = k) (h : k = k') :
    Orientation.reindex ℝ V (finCongr h) (ω.orientation hk) = ω.orientation (hk.trans h) := by
  subst h
  simp

/-- The symplectic orientation of the standard symplectic form
`ω₀((s₁, t₁), (s₂, t₂)) = s₁ t₂ - t₁ s₂` on the plane `ℝ × ℝ` is the orientation of the standard
basis `((1, 0), (0, 1))`. -/
@[simp]
theorem orientation_stdSymplecticForm_real (hk : finrank ℝ (ℝ × ℝ) = 2) :
    (stdSymplecticForm (V := ℝ)).orientation hk = (Basis.finTwoProd ℝ).orientation := by
  have h : 1 * 2 = 2 := rfl
  let e : Fin 1 × Fin 2 ≃ Fin 2 := finProdFinEquiv.trans (finCongr h)
  have hb : (stdSymplecticForm (V := ℝ)).IsDarbouxBasis ((Basis.finTwoProd ℝ).reindex e.symm) := by
    -- The Darboux pair is `q = (1, 0)` and `p = (0, 1)`.
    have h₀ : finProdFinEquiv ((0 : Fin 1), (0 : Fin 2)) = 0 := rfl
    have h₁ : finProdFinEquiv ((0 : Fin 1), (1 : Fin 2)) = 1 := rfl
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;> fin_cases i <;> fin_cases j <;>
      simp [e, stdSymplecticForm_apply, h₀, h₁]
  rw [← hb.orientation_reindex hk h]
  congr 1
  exact Basis.eq_of_apply_eq fun i ↦ by simp [e]

/-- The symplectic orientation of `ds ∧ dt + ω` on `ℝ × (ℝ × V)`, the direct sum of the standard
symplectic form of the plane `ℝ²_(s,t)` with `ω`, reassociated, is the product of the standard
orientation of `ℝ` (the `s`-direction), the standard orientation of `ℝ` (the `t`-direction) and the
symplectic orientation of `ω`. -/
theorem orientation_transport_prodAssoc_stdSymplecticForm_prod (ω : SymplecticForm V) {m : ℕ}
    (hm : finrank ℝ V = m) (hk : finrank ℝ (ℝ × (ℝ × V)) = 1 + (1 + m)) :
    (((stdSymplecticForm (V := ℝ)).prod ω).transport
        (LinearEquiv.prodAssoc ℝ ℝ ℝ V)).orientation hk =
      Orientation.prod (Basis.singleton (Fin 1) ℝ).orientation
        (Orientation.prod (Basis.singleton (Fin 1) ℝ).orientation (ω.orientation hm)
          (finrank_self ℝ) hm)
        (finrank_self ℝ) (by rw [finrank_prod, finrank_self, hm]) := by
  have h₂ : finrank ℝ (ℝ × ℝ) = 1 + 1 := by rw [finrank_prod, finrank_self]
  have hk' : finrank ℝ ((ℝ × ℝ) × V) = 1 + 1 + m := by rw [finrank_prod, h₂, hm]
  -- Reassociating carries `ds ∧ dt ⊕ ω` to `ds ∧ dt + ω`, and its orientation to theirs.
  have h := (isSymplectomorphism_iff_transport_eq.2 rfl :
    IsSymplectomorphism ((stdSymplecticForm (V := ℝ)).prod ω) _
      (LinearEquiv.prodAssoc ℝ ℝ ℝ V)).map_orientation hk'
  rw [orientation_prod _ _ h₂ hm hk', orientation_stdSymplecticForm_real h₂,
    ← Orientation.prod_singleton_orientation, Orientation.map_prodAssoc_prod] at h
  have hk'' : finrank ℝ (ℝ × (ℝ × V)) = 1 + 1 + m := hk.trans (add_assoc 1 1 m).symm
  rw [← reindex_orientation _ hk'' (add_assoc 1 1 m), ← h,
    ← finCongr_symm (add_assoc 1 1 m).symm, ← Orientation.reindex_symm, Equiv.symm_apply_apply]

/-! ### Tamed almost complex structures -/

variable {J : AlmostComplexStructure V}

/-- One step of the symplectic Gram–Schmidt process for a tamed almost complex structure. If `S`
is `J`-invariant and `v ∉ S`, there is a pair `(x, y)` in the symplectic complement of `S` with
`ω x y = 1`, `x ≡ v` and `y ≡ c • J v` modulo `S` for some `c > 0`. -/
private theorem Tames.exists_pair (hJ : ω.Tames J) {S : Submodule ℝ V}
    (hS : S ∈ Module.End.invtSubmodule J.toLinearMap) {v : V} (hv : v ∉ S) :
    ∃ x y : V, x ∈ ω.orthogonal S ∧ y ∈ ω.orthogonal S ∧ ω x y = 1 ∧ x - v ∈ S ∧
      ∃ c : ℝ, 0 < c ∧ y - c • J v ∈ S := by
  have hc := (hJ.isSymplectic_of_mem_invtSubmodule hS).isCompl.symm
  set π := (ω.orthogonal S).projection S hc
  -- `x` is the component of `v` in the symplectic complement, and `z` that of `J x`.
  set x := π v
  set z := π (J x)
  have hxv : v - x ∈ S := Submodule.sub_projection_mem hc v
  have hzx : J x - z ∈ S := Submodule.sub_projection_mem hc (J x)
  have hxo : x ∈ ω.orthogonal S := Submodule.projection_apply_mem hc v
  have hx0 : x ≠ 0 := by
    rintro hx
    rw [hx, sub_zero] at hxv
    exact hv hxv
  have hpos : 0 < ω x (J x) := hJ x hx0
  -- `ω x z = ω x (J x)`, because `J x - z ∈ S` and `x ∈ S^ω`.
  have hxz : ω x z = ω x (J x) := by
    have := (mem_orthogonal_iff'.1 hxo) _ hzx
    simp only [map_sub] at this
    linarith
  refine ⟨x, (ω x (J x))⁻¹ • z, hxo, Submodule.smul_mem _ _ (Submodule.projection_apply_mem hc _),
    ?_, ?_, (ω x (J x))⁻¹, inv_pos.2 hpos, ?_⟩
  · simp only [map_smul, smul_eq_mul, hxz]
    exact inv_mul_cancel₀ hpos.ne'
  · rw [← neg_sub]
    exact neg_mem hxv
  · rw [← smul_sub]
    refine Submodule.smul_mem _ _ ?_
    have : z - J v = -(J x - z) - J (v - x) := by
      rw [map_sub]
      abel
    rw [this]
    exact sub_mem (neg_mem hzx) ((Module.End.mem_invtSubmodule _).1 hS hxv)

/-- **A tamed almost complex structure determines the symplectic orientation.** If `ω` tames `J`,
then every `J`-adapted basis `(v₁, J v₁, …, vₙ, J vₙ)`, listed in this interleaved order, is
positive for the symplectic orientation of `ω`. -/
theorem Tames.orientation_reindex (hJ : ω.Tames J) (hb : ∀ i, b (i, 1) = J (b (i, 0)))
    (hk : finrank ℝ V = k) (h : n * 2 = k) :
    (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation = ω.orientation hk := by
  -- `S i` is spanned by the first `i` adapted pairs; it is `J`-invariant.
  set S : Fin n → Submodule ℝ V := fun i ↦ Submodule.span ℝ (b '' {r | r.1 < i})
  have hbS {r : Fin n × Fin 2} {i : Fin n} (h : r.1 < i) : b r ∈ S i :=
    Submodule.subset_span ⟨r, h, rfl⟩
  have hSmono {i j : Fin n} (h : i ≤ j) : S i ≤ S j :=
    Submodule.span_mono (Set.image_mono fun _ hr ↦ lt_of_lt_of_le hr h)
  have hS (i : Fin n) : S i ∈ Module.End.invtSubmodule J.toLinearMap :=
    J.span_image_fst_lt_mem_invtSubmodule hb i
  have hv (i : Fin n) : b (i, 0) ∉ S i := fun h ↦
    lt_irrefl i ((Basis.mem_span_image b).1 h (by simp : (i, 0) ∈ (b.repr (b (i, 0))).support))
  choose x y hx hy hxy hxv c hc hyv using fun i ↦ hJ.exists_pair (hS i) (hv i)
  set d : Fin n × Fin 2 → V := fun p ↦ ![x p.1, y p.1] p.2
  -- The pairs before the `i`-th lie in `S i`, and the `i`-th pair lies in its complement.
  have hdS (p : Fin n × Fin 2) {i : Fin n} (hi : p.1 < i) : d p ∈ S i := by
    obtain ⟨j, a⟩ := p
    fin_cases a
    · simpa [d] using add_mem (hSmono hi.le (hxv j)) (hbS (r := (j, 0)) hi)
    · simpa [d, hb] using
        add_mem (hSmono hi.le (hyv j)) (Submodule.smul_mem _ (c j) (hbS (r := (j, 1)) hi))
  have hdo (p : Fin n × Fin 2) : d p ∈ ω.orthogonal (S p.1) := by
    obtain ⟨j, a⟩ := p
    fin_cases a
    · simpa [d] using hx j
    · simpa [d] using hy j
  have hcross (p q : Fin n × Fin 2) (hpq : p.1 ≠ q.1) : ω (d p) (d q) = 0 := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact (mem_orthogonal_iff.1 (hdo q)) _ (hdS p h)
    · exact (mem_orthogonal_iff'.1 (hdo p)) _ (hdS q h)
  -- In the basis `b`, the family `d` is triangular with diagonal entries `1` and `c i`.
  have hcoef (p : Fin n × Fin 2) : 0 < ![1, c p.1] p.2 := by
    obtain ⟨j, a⟩ := p
    fin_cases a
    · simp
    · simpa using hc j
  have htri (p : Fin n × Fin 2) :
      d p - ![1, c p.1] p.2 • b p ∈ Submodule.span ℝ (b '' {r | r.1 < p.1}) := by
    obtain ⟨j, a⟩ := p
    fin_cases a
    · simpa [d] using hxv j
    · simpa [d, hb] using hyv j
  -- Listed lexicographically, `d` is triangular in the sense of
  -- `Module.Basis.det_pos_of_sub_smul_mem_span`.
  have hdet : 0 < b.det d := by
    rw [show b.det d = (b.reindex toLex).det (d ∘ ofLex) by rw [Basis.det_reindex]; rfl]
    refine (b.reindex toLex).det_pos_of_sub_smul_mem_span (fun p ↦ hcoef (ofLex p)) fun p ↦ ?_
    refine Submodule.span_mono ?_ (by simpa using htri (ofLex p))
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨toLex q, Prod.Lex.toLex_lt_toLex.2 (.inl hq), by simp⟩
  have hbasis := b.is_basis_iff_det.2 hdet.ne'.isUnit
  set D := Basis.mk hbasis.1 hbasis.2.ge
  have hDd : ⇑D = d := Basis.coe_mk _ _
  have hD : ω.IsDarbouxBasis D := by
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_, fun i j ↦ ?_⟩ <;> rw [hDd] <;>
      rcases eq_or_ne i j with rfl | hij
    · simp
    · exact hcross (i, 0) (j, 0) hij
    · simp
    · exact hcross (i, 1) (j, 1) hij
    · simpa [d] using hxy i
    · simpa [hij] using hcross (i, 0) (j, 1) hij
  rw [← hD.orientation_reindex hk h, Basis.orientation_reindex, Basis.orientation_reindex,
    (b.orientation_eq_iff_det_pos D).2 (by rwa [hDd])]

/-- **Symplectic forms taming a common almost complex structure have the same symplectic
orientation.** -/
theorem Tames.orientation_eq (hJ : ω.Tames J) {ω' : SymplecticForm V} (hJ' : ω'.Tames J)
    (hk : finrank ℝ V = k) : ω.orientation hk = ω'.orientation hk := by
  obtain ⟨n, b, hb⟩ := J.exists_basis_apply_one_eq
  have h : n * 2 = k := by simp [← hk, Module.finrank_eq_card_basis b]
  rw [← hJ.orientation_reindex hb hk h, hJ'.orientation_reindex hb hk h]

end SymplecticForm

end TauCeti
