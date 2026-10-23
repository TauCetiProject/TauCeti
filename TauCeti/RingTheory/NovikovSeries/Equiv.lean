/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Changing the period map of a Novikov ring

An additive equivalence of exponent monoids which rescales periods by a positive constant
induces an algebra equivalence of Novikov rings. Its coefficient formula and exact transport
of the period filtration show that it is a homeomorphism for the period topologies.

In particular, positive rescaling of the period map preserves every coefficient, whereas
reversing the period map transports the coefficient at `h` to `-h`. The latter comparison
reverses the direction of completion; it does not identify the two coefficient functions.
Thus positive rescaling changes the potential scale without changing coefficients, while
period reversal changes deck-group conventions by reindexing coefficients along negation.

The construction uses the pushforward and its composition law from
`TauCeti.RingTheory.NovikovSeries.Map`, together with the algebra-homomorphism and continuity APIs
from
`TauCeti.RingTheory.NovikovSeries.Functoriality`.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

noncomputable section

namespace TauCeti.NovikovSeries

variable (A : Type*) {R H H' H'' : Type*} [CommSemiring A]

section Reindex

variable [AddMonoid H] [AddMonoid H'] {N : H →+ ℝ} {N' : H' →+ ℝ}

private theorem period_rescale_symm (e : H ≃+ H') {c : ℝ} (hc : 0 < c)
    (hcN : ∀ h, N' (e h) = c * N h) (h' : H') :
    N (e.symm h') = c⁻¹ * N' h' := by
  have h := hcN (e.symm h')
  rw [e.apply_symm_apply] at h
  rw [h, inv_mul_cancel_left₀ hc.ne']

private theorem exists_period_rescale_symm (e : H ≃+ H')
    (he : ∃ c > 0, ∀ h, N' (e h) = c * N h) :
    ∃ c > 0, ∀ h', N (e.symm h') = c * N' h' := by
  obtain ⟨c, hc, hcN⟩ := he
  exact ⟨c⁻¹, inv_pos.mpr hc, period_rescale_symm e hc hcN⟩

section Algebra

variable [Semiring R] [Algebra A R] (e : H ≃+ H')
  (he : ∃ c > 0, ∀ h, N' (e h) = c * N h)

/-- Reindex Novikov series by an additive equivalence rescaling periods positively.
The inverse is pushforward along the inverse equivalence. -/
def domCongr : NovikovSeries R H N ≃ₐ[A] NovikovSeries R H' N' where
  __ := mapAlgHom (AlgHom.id A R) (e : H →+ H') he
  toFun := mapAlgHom (AlgHom.id A R) (e : H →+ H') he
  invFun := mapAlgHom (AlgHom.id A R) (e.symm : H' →+ H)
    (exists_period_rescale_symm e he)
  left_inv a := by
    simp only [mapAlgHom_apply, AlgHom.id_toRingHom, RingHom.toAddMonoidHom_id,
      map_map, AddMonoidHom.id_comp, AddEquiv.toAddMonoidHom_symm_comp_toAddMonoidHom,
      map_id, AddMonoidHom.id_apply]
  right_inv b := by
    simp only [mapAlgHom_apply, AlgHom.id_toRingHom, RingHom.toAddMonoidHom_id,
      map_map, AddMonoidHom.id_comp, AddEquiv.toAddMonoidHom_comp_toAddMonoidHom_symm,
      map_id, AddMonoidHom.id_apply]

theorem domCongr_apply (a : NovikovSeries R H N) :
    domCongr A e he a = map ((AlgHom.id A R : R →+* R) : R →+ R) (e : H →+ H') he a :=
  mapAlgHom_apply (AlgHom.id A R) (e : H →+ H') he a

private theorem domCongr_symm_apply (b : NovikovSeries R H' N') :
    (domCongr A e he).symm b =
      map ((AlgHom.id A R : R →+* R) : R →+ R) (e.symm : H' →+ H)
        (exists_period_rescale_symm e he) b :=
  mapAlgHom_apply (AlgHom.id A R) (e.symm : H' →+ H) _ b

/-- Reindexing moves the coefficient at `h` to `e h`. -/
@[simp]
theorem coeff_domCongr (a : NovikovSeries R H N) (h' : H') :
    (domCongr A e he a).coeff h' = a.coeff (e.symm h') := by
  obtain ⟨h, rfl⟩ := e.surjective h'
  rw [domCongr_apply]
  simpa using coeff_map_of_injective ((AlgHom.id A R : R →+* R) : R →+ R)
    (e : H →+ H') he e.injective a h

/-- The inverse comparison restricts coefficients along `e`. -/
@[simp]
theorem coeff_domCongr_symm (b : NovikovSeries R H' N') (h : H) :
    ((domCongr A e he).symm b).coeff h = b.coeff (e h) := by
  obtain ⟨h', rfl⟩ := e.symm.surjective h
  simpa [domCongr_symm_apply] using
    coeff_map_of_injective ((AlgHom.id A R : R →+* R) : R →+ R)
      (e.symm : H' →+ H) (exists_period_rescale_symm e he) e.symm.injective b h'

/-- Reindexing carries monomials to monomials with the corresponding exponent. -/
@[simp]
theorem domCongr_single (h : H) (r : R) :
    domCongr A e he (single h r) = single (e h) r := by
  simp [domCongr_apply, map_single]

/-- Inverse reindexing carries monomials along the inverse exponent equivalence. -/
@[simp]
theorem domCongr_symm_single (h' : H') (r : R) :
    (domCongr A e he).symm (single h' r) = single (e.symm h') r := by
  apply (domCongr A e he).injective
  simp

/-- Reindexing by the identity is the identity algebra equivalence. -/
@[simp]
theorem domCongr_refl :
    domCongr A (R := R) (N := N) (AddEquiv.refl H) ⟨1, one_pos, by simp⟩ =
      AlgEquiv.refl := by
  ext a h
  rw [coeff_domCongr]
  rfl

/-- Successive reindexings compose along the composite exponent equivalence. -/
theorem domCongr_trans [AddMonoid H''] {N'' : H'' →+ ℝ} (e' : H' ≃+ H'')
    (he' : ∃ c > 0, ∀ h, N'' (e' h) = c * N' h) :
    (domCongr A (R := R) e he).trans (domCongr A e' he') =
      domCongr A (e.trans e') (by
        simpa only [AddEquiv.trans_apply, AddMonoidHom.comp_apply,
          AddEquiv.coe_toAddMonoidHom] using
          exists_period_rescale_comp (φ := e.toAddMonoidHom) (φ' := e'.toAddMonoidHom)
            (by simpa only [AddEquiv.coe_toAddMonoidHom] using he)
            (by simpa only [AddEquiv.coe_toAddMonoidHom] using he')) := by
  ext a h
  simp

end Algebra

section Topology

variable [Ring R] [Algebra A R] (e : H ≃+ H')
  (he : ∃ c > 0, ∀ h, N' (e h) = c * N h)

/-- Reindexing identifies the period neighbourhood at `C` with that at `c * C`. -/
theorem domCongr_mem_periodFiltration_iff {c C : ℝ} (hc : 0 < c)
    (hcN : ∀ h, N' (e h) = c * N h) (a : NovikovSeries R H N) :
    domCongr A e ⟨c, hc, hcN⟩ a ∈ periodFiltration R N' (c * C) ↔
      a ∈ periodFiltration R N C := by
  constructor
  · intro ha
    have hb := map_mem_periodFiltration ((AlgHom.id A R : R →+* R) : R →+ R)
      (e.symm : H' →+ H) (exists_period_rescale_symm e ⟨c, hc, hcN⟩)
      (inv_pos.mpr hc).le (period_rescale_symm e hc hcN) ha
    rw [← domCongr_symm_apply A e ⟨c, hc, hcN⟩] at hb
    simpa [hc.ne'] using hb
  · intro ha
    rw [domCongr_apply]
    exact map_mem_periodFiltration ((AlgHom.id A R : R →+* R) : R →+ R)
      (e : H →+ H') ⟨c, hc, hcN⟩ hc.le hcN ha

/-- Positive period-rescaling reindexings are isomorphisms of topological algebras. -/
def continuousDomCongr : NovikovSeries R H N ≃A[A] NovikovSeries R H' N' where
  __ := domCongr A e he
  toFun := domCongr A e he
  continuous_toFun :=
    (continuous_map ((AlgHom.id A R : R →+* R) : R →+ R) (e : H →+ H') he).congr
      fun a => (domCongr_apply A e he a).symm
  continuous_invFun :=
    (continuous_map ((AlgHom.id A R : R →+* R) : R →+ R) (e.symm : H' →+ H)
      (exists_period_rescale_symm e he)).congr
      fun b => (domCongr_symm_apply A e he b).symm

@[simp]
theorem continuousDomCongr_apply (a : NovikovSeries R H N) :
    continuousDomCongr A e he a = domCongr A e he a :=
  (rfl)

@[simp]
theorem continuousDomCongr_symm_apply (b : NovikovSeries R H' N') :
    (continuousDomCongr A e he).symm b = (domCongr A e he).symm b :=
  (rfl)

/-- Reindexing by the identity is the identity topological algebra equivalence. -/
@[simp]
theorem continuousDomCongr_refl :
    continuousDomCongr A (R := R) (N := N) (AddEquiv.refl H) ⟨1, one_pos, by simp⟩ =
      ContinuousAlgEquiv.refl A _ := by
  ext a h
  rw [continuousDomCongr_apply, coeff_domCongr]
  rfl

/-- Successive continuous reindexings compose along the exponent equivalences. -/
theorem continuousDomCongr_trans [AddMonoid H''] {N'' : H'' →+ ℝ} (e' : H' ≃+ H'')
    (he' : ∃ c > 0, ∀ h, N'' (e' h) = c * N' h) :
    (continuousDomCongr A (R := R) e he).trans (continuousDomCongr A e' he') =
      continuousDomCongr A (e.trans e') (by
        simpa only [AddEquiv.trans_apply, AddMonoidHom.comp_apply,
          AddEquiv.coe_toAddMonoidHom] using
          exists_period_rescale_comp (φ := e.toAddMonoidHom) (φ' := e'.toAddMonoidHom)
            (by simpa only [AddEquiv.coe_toAddMonoidHom] using he)
            (by simpa only [AddEquiv.coe_toAddMonoidHom] using he')) := by
  ext a h
  simp

end Topology

end Reindex

section Rescale

variable [AddMonoid H] [Ring R] [Algebra A R] (N : H →+ ℝ) {c : ℝ} (hc : 0 < c)

/-- Positive rescaling of the period map gives the same completed algebra and topology,
by the coefficient-preserving comparison. -/
def rescaleContinuousAlgEquiv : NovikovSeries R H N ≃A[A] NovikovSeries R H (c • N) :=
  continuousDomCongr A (AddEquiv.refl H) ⟨c, hc, fun _ => rfl⟩

@[simp]
theorem coeff_rescaleContinuousAlgEquiv (a : NovikovSeries R H N) (h : H) :
    (rescaleContinuousAlgEquiv A N hc a).coeff h = a.coeff h := by
  simp [rescaleContinuousAlgEquiv]

@[simp]
theorem coeff_rescaleContinuousAlgEquiv_symm (a : NovikovSeries R H (c • N)) (h : H) :
    ((rescaleContinuousAlgEquiv A N hc).symm a).coeff h = a.coeff h := by
  simp [rescaleContinuousAlgEquiv]

/-- Positive rescaling fixes every monomial. -/
@[simp]
theorem rescaleContinuousAlgEquiv_single (h : H) (r : R) :
    rescaleContinuousAlgEquiv A N hc (single h r) = single h r := by
  simp [rescaleContinuousAlgEquiv]

/-- The inverse positive rescaling comparison fixes every monomial. -/
@[simp]
theorem rescaleContinuousAlgEquiv_symm_single (h : H) (r : R) :
    (rescaleContinuousAlgEquiv A N hc).symm (single h r) = single h r := by
  simp [rescaleContinuousAlgEquiv]

/-- Under positive rescaling, the cutoff `C` becomes `c * C`. -/
theorem rescaleContinuousAlgEquiv_mem_periodFiltration_iff (C : ℝ)
    (a : NovikovSeries R H N) :
    rescaleContinuousAlgEquiv A N hc a ∈ periodFiltration R (c • N) (c * C) ↔
      a ∈ periodFiltration R N C :=
  domCongr_mem_periodFiltration_iff A (AddEquiv.refl H) hc (fun _ => rfl) a

end Rescale

section Reverse

variable [AddCommGroup H] [Ring R] [Algebra A R] (N : H →+ ℝ)

/-- Reversing periods gives a topological algebra isomorphism by negating exponents.
In particular, this map sends `e^h` to `e^(-h)`. -/
def reverseContinuousAlgEquiv : NovikovSeries R H N ≃A[A] NovikovSeries R H (-N) :=
  continuousDomCongr A (AddEquiv.neg H) ⟨1, one_pos, by simp⟩

@[simp]
theorem coeff_reverseContinuousAlgEquiv (a : NovikovSeries R H N) (h : H) :
    (reverseContinuousAlgEquiv A N a).coeff h = a.coeff (-h) := by
  simp [reverseContinuousAlgEquiv]

@[simp]
theorem coeff_reverseContinuousAlgEquiv_symm (a : NovikovSeries R H (-N)) (h : H) :
    ((reverseContinuousAlgEquiv A N).symm a).coeff h = a.coeff (-h) := by
  simp [reverseContinuousAlgEquiv]

/-- Period reversal negates the exponent of every monomial. -/
@[simp]
theorem reverseContinuousAlgEquiv_single (h : H) (r : R) :
    reverseContinuousAlgEquiv A N (single h r) = single (-h) r := by
  simp [reverseContinuousAlgEquiv]

/-- The inverse period reversal comparison negates every monomial exponent. -/
@[simp]
theorem reverseContinuousAlgEquiv_symm_single (h : H) (r : R) :
    (reverseContinuousAlgEquiv A N).symm (single h r) = single (-h) r := by
  simp [reverseContinuousAlgEquiv]

/-- Period reversal preserves cutoffs when accompanied by exponent negation. -/
theorem reverseContinuousAlgEquiv_mem_periodFiltration_iff (C : ℝ)
    (a : NovikovSeries R H N) :
    reverseContinuousAlgEquiv A N a ∈ periodFiltration R (-N) C ↔
      a ∈ periodFiltration R N C := by
  simpa only [reverseContinuousAlgEquiv, continuousDomCongr_apply, one_mul] using
    domCongr_mem_periodFiltration_iff A (AddEquiv.neg H)
      (N' := -N) one_pos (by simp) (C := C) a

end Reverse

end TauCeti.NovikovSeries
