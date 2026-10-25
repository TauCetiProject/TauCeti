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
induces an algebra equivalence of Novikov rings. This equivalence is a homeomorphism for the
period topologies and sends the period neighbourhood `U_C` exactly onto `U_(c * C)`.

In particular, positive rescaling of the period map preserves every coefficient, whereas
reversing the period map transports the coefficient at `h` to `-h`. The latter comparison
reverses the direction of completion; it does not identify the two coefficient functions.
Thus positive rescaling changes the potential scale without changing coefficients, while
period reversal changes deck-group conventions by reindexing coefficients along negation.

These equivalences are the invertible special case of `NovikovSeries.map`.
Inverse coefficient and monomial formulas follow by simplification with `domCongr_symm`
and `continuousDomCongr_symm`, followed by the corresponding forward formulas.

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

section Algebra

variable [Semiring R] [Algebra A R] (e : H ≃+ H')
  (he : ∃ c > 0, ∀ h, N' (e h) = c * N h)

/-- Reindex Novikov series by an additive equivalence rescaling periods positively.
The inverse is pushforward along the inverse equivalence. -/
def domCongr : NovikovSeries R H N ≃ₐ[A] NovikovSeries R H' N' where
  __ := mapAlgHom (AlgHom.id A R) (e : H →+ H') he
  toFun := mapAlgHom (AlgHom.id A R) (e : H →+ H') he
  invFun := mapAlgHom (AlgHom.id A R) (e.symm : H' →+ H)
    (exists_period_rescale_symm (e := e) he)
  left_inv a := by
    simp [mapAlgHom_apply, map_map, map_id]
  right_inv b := by
    simp [mapAlgHom_apply, map_map, map_id]

theorem domCongr_apply (a : NovikovSeries R H N) :
    domCongr A e he a = map ((AlgHom.id A R : R →+* R) : R →+ R) (e : H →+ H') he a :=
  mapAlgHom_apply (AlgHom.id A R) (e : H →+ H') he a

/-- Inverse reindexing is reindexing by the inverse exponent equivalence. -/
@[simp]
theorem domCongr_symm :
    (domCongr A (R := R) e he).symm =
      domCongr A e.symm (exists_period_rescale_symm he) := by
  ext b h
  simp [domCongr]

private theorem domCongr_symm_apply (b : NovikovSeries R H' N') :
    (domCongr A e he).symm b =
      map ((AlgHom.id A R : R →+* R) : R →+ R) (e.symm : H' →+ H)
        (exists_period_rescale_symm (e := e) he) b := by
  rw [domCongr_symm, domCongr_apply]

/-- Reindexing moves the coefficient at `h` to `e h`. -/
@[simp]
theorem coeff_domCongr (a : NovikovSeries R H N) (h' : H') :
    (domCongr A e he a).coeff h' = a.coeff (e.symm h') := by
  obtain ⟨h, rfl⟩ := e.surjective h'
  rw [domCongr_apply]
  simpa using coeff_map_of_injective ((AlgHom.id A R : R →+* R) : R →+ R)
    (e : H →+ H') he e.injective a h

/-- Reindexing carries monomials to monomials with the corresponding exponent. -/
@[simp]
theorem domCongr_single (h : H) (r : R) :
    domCongr A e he (single h r) = single (e h) r := by
  simp [domCongr_apply, map_single]

/-- Reindexing by the identity is the identity algebra equivalence. -/
@[simp]
theorem domCongr_refl :
    domCongr A (R := R) (N := N) (AddEquiv.refl H) ⟨1, one_pos, by simp⟩ =
      AlgEquiv.refl := by
  ext a h
  simp

/-- Successive reindexings compose along the composite exponent equivalence. -/
theorem domCongr_trans [AddMonoid H''] {N'' : H'' →+ ℝ} (e' : H' ≃+ H'')
    (he' : ∃ c > 0, ∀ h, N'' (e' h) = c * N' h) :
    (domCongr A (R := R) e he).trans (domCongr A e' he') =
      domCongr A (e.trans e') (by exact exists_period_rescale_trans he he') := by
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
      (e.symm : H' →+ H) (exists_period_rescale_symm (e := e) ⟨c, hc, hcN⟩)
      (inv_pos.mpr hc).le (period_rescale_symm hc hcN) ha
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
      (exists_period_rescale_symm (e := e) he)).congr
      fun b => (domCongr_symm_apply A e he b).symm

@[simp]
theorem continuousDomCongr_apply (a : NovikovSeries R H N) :
    continuousDomCongr A e he a = domCongr A e he a :=
  (rfl)

/-- The inverse continuous comparison reindexes by the inverse exponent equivalence. -/
@[simp]
theorem continuousDomCongr_symm :
    (continuousDomCongr A (R := R) e he).symm =
      continuousDomCongr A e.symm (exists_period_rescale_symm he) := by
  ext b h
  -- Unfold the continuous wrapper and its inverse to expose the underlying algebra equivalence.
  change ((domCongr A e he).symm b).coeff h =
    (domCongr A e.symm (exists_period_rescale_symm he) b).coeff h
  simp

/-- Reindexing by the identity is the identity topological algebra equivalence. -/
@[simp]
theorem continuousDomCongr_refl :
    continuousDomCongr A (R := R) (N := N) (AddEquiv.refl H) ⟨1, one_pos, by simp⟩ =
      ContinuousAlgEquiv.refl A _ := by
  ext a h
  simp

/-- Successive continuous reindexings compose along the exponent equivalences. -/
theorem continuousDomCongr_trans [AddMonoid H''] {N'' : H'' →+ ℝ} (e' : H' ≃+ H'')
    (he' : ∃ c > 0, ∀ h, N'' (e' h) = c * N' h) :
    (continuousDomCongr A (R := R) e he).trans (continuousDomCongr A e' he') =
      continuousDomCongr A (e.trans e') (by exact exists_period_rescale_trans he he') := by
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
