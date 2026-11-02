/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Eigenvector
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.ContravariantForm
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Weight.HighestWeight
import TauCeti.RepresentationTheory.ContravariantForm

/-!
# The Gelfand–Tsetlin basis of a rational Weyl module

The rational Weyl module `V_λ` of `GL n ℂ` is the internal direct sum of the Gelfand–Tsetlin lines
`TauCeti.gtLine λ P`, one for each pattern `P` with top weight `λ`. This file shows that the lines
are pairwise orthogonal for the contravariant Hermitian form `TauCeti.weylForm`, and constructs the
**Gelfand–Tsetlin basis** `TauCeti.gtBasis`: a basis of `V_λ` indexed by the patterns, whose vector
at `P` is a generator of the line of `P` of norm one.

The form determines each vector up to a complex scalar of absolute value one
(`TauCeti.exists_norm_eq_one_and_eq_smul_gtBasis`). These phases are not normalized here: the
vectors are chosen generators, and the characteristic properties of the basis are the ones stated
below.

The orthogonality is proved by induction on `n`. The restriction of `V_λ` to `GL (n - 1) ℂ` is a sum
of pairwise nonisomorphic irreducibles `V_μ`, and the adjoint of an intertwiner is again an
intertwiner because the form is contravariant. So Schur's lemma says that the images of `V_μ` and
`V_ν` for `μ ≠ ν` are orthogonal (`TauCeti.weylForm_intertwiningMap_apply_eq_zero`), and that an
intertwiner from `V_μ` scales the form (`TauCeti.exists_forall_weylForm_intertwiningMap_apply_eq`),
which carries the orthogonality of the lines of `V_μ` to their images.

## Main definitions

* `TauCeti.gtBasis`: the Gelfand–Tsetlin basis of `V_λ`.

## Main results

* `TauCeti.weylForm_eq_zero_of_mem_gtLine`: the Gelfand–Tsetlin lines are pairwise orthogonal.
* `TauCeti.gtBasis_mem_gtLine`, `TauCeti.span_singleton_gtBasis`: each basis vector generates the
  line of its pattern.
* `TauCeti.weylForm_gtBasis_self`, `TauCeti.weylForm_gtBasis_of_ne`: the basis is orthonormal.
* `TauCeti.gtBasis_repr_apply`: its coordinates are computed by the form.
* `TauCeti.exists_norm_eq_one_and_eq_smul_gtBasis`: uniqueness up to phases.
* `TauCeti.lift_differential_gelfandTsetlinGenerator_apply_gtBasis`: the Gelfand–Tsetlin generators
  are diagonal in the basis.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Gelfand-Tsetlin bases for classical Lie algebras*, in Handbook of Algebra, Vol. 4
  (2006), 109–170, §2, where the basis is normalized through a contravariant form.
-/

public section

open Module Representation
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

section Branching

variable {n : ℕ} {l : DominantWeight (n + 1)} {m m' : DominantWeight n}

/-- The pairing of `V_m` and `V_m'` obtained from two intertwiners to the restriction of `V_l` is
contravariant. -/
private theorem weylForm_intertwiningMap_contravariant
    (f : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
    (h : IntertwiningMap (rationalWeylRep ℂ n m')
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) (g : GL (Fin n) ℂ)
    (x : (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (y : (weylModuleOfShape ℂ n m'.detShiftShape).toSubmodule) :
    (((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap)
        (rationalWeylRep ℂ n m g x) y =
      (((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap) x
        (rationalWeylRep ℂ n m' (star g) y) := by
  simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, IntertwiningMap.coe_toLinearMap,
    IntertwiningMap.isIntertwining, MonoidHom.comp_apply, weylForm_rationalWeylRep_apply,
    glBlockSucc_star]

/-- **Branching summands are orthogonal.** The images of two nonisomorphic constituents `V_m` and
`V_m'` of the restriction of `V_l` to `GL n ℂ` are orthogonal for the contravariant form. -/
theorem weylForm_intertwiningMap_apply_eq_zero (hm : m ≠ m')
    (f : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
    (h : IntertwiningMap (rationalWeylRep ℂ n m')
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
    (x : (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (y : (weylModuleOfShape ℂ n m'.detShiftShape).toSubmodule) :
    weylForm (n + 1) l.detShiftShape (f x) (h y) = 0 := by
  have hE : IsEmpty ((rationalWeylRep ℂ n m').Equiv (rationalWeylRep ℂ n m)) :=
    ⟨fun e ↦ hm ((nonempty_equiv_rationalWeylRep_iff ℂ).mp ⟨e⟩).symm⟩
  have hS := eq_zero_of_isEmpty_equiv (𝕜 := ℂ)
    (V := (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule)
    (W := (weylModuleOfShape ℂ n m'.detShiftShape).toSubmodule)
    (rationalWeylRep ℂ n m) (rationalWeylRep ℂ n m')
    (B := weylForm n m.detShiftShape)
    (S := ((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap)
    (isSymm_weylForm _) (fun _ hx ↦ weylForm_apply_self_pos hx) (weylForm_rationalWeylRep_apply m)
    (weylForm_intertwiningMap_contravariant f h) hE
  exact LinearMap.congr_fun₂ hS x y

/-- **An embedding of a branching summand scales the form.** Two intertwiners from `V_m` to the
restriction of `V_l` to `GL n ℂ` pull the contravariant form of `V_l` back to a scalar multiple of
that of `V_m`. -/
theorem exists_forall_weylForm_intertwiningMap_apply_eq
    (f h : IntertwiningMap (rationalWeylRep ℂ n m)
      ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n))) :
    ∃ c : ℂ, ∀ x y, weylForm (n + 1) l.detShiftShape (f x) (h y) = c * weylForm n _ x y :=
  exists_forall_apply_eq_mul_apply (𝕜 := ℂ)
    (V := (weylModuleOfShape ℂ n m.detShiftShape).toSubmodule) (rationalWeylRep ℂ n m)
    (B := weylForm n m.detShiftShape)
    (S := ((weylForm (n + 1) l.detShiftShape).comp f.toLinearMap).compl₂ h.toLinearMap)
    (isSymm_weylForm _) (fun _ hx ↦ weylForm_apply_self_pos hx) (weylForm_rationalWeylRep_apply m)
    (weylForm_intertwiningMap_contravariant f h)

end Branching

/-- **The Gelfand–Tsetlin lines are pairwise orthogonal** for the contravariant form of `V_λ`. -/
theorem weylForm_eq_zero_of_mem_gtLine : ∀ {n : ℕ} (l : DominantWeight n)
    {P Q : {P : GTPattern n // P.topWeight = l}}, P ≠ Q →
    ∀ {x y : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule},
      x ∈ gtLine l P → y ∈ gtLine l Q → weylForm n _ x y = 0
  | 0, _, P, Q, hPQ, _, _, _, _ => absurd (Subsingleton.elim P Q) hPQ
  | n + 1, l, P, Q, hPQ, x, y, hx, hy => by
    -- The weights of the second rows are arbitrary below, which allows the case of equal weights
    -- to be separated without transporting along their equality.
    have key : ∀ {m m' : DominantWeight n}
        (f : IntertwiningMap (rationalWeylRep ℂ n m)
          ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
        (h : IntertwiningMap (rationalWeylRep ℂ n m')
          ((rationalWeylRep ℂ (n + 1) l).comp (glBlockSucc ℂ n)))
        (P' : {R : GTPattern n // R.topWeight = m}) (Q' : {R : GTPattern n // R.topWeight = m'}),
        P'.1 ≠ Q'.1 → ∀ {x' y'}, x' ∈ gtLine m P' → y' ∈ gtLine m' Q' →
          weylForm (n + 1) l.detShiftShape (f x') (h y') = 0 := by
      intro m m' f h P' Q' hne x' y' hx' hy'
      rcases eq_or_ne m m' with rfl | hm
      · obtain ⟨c, hc⟩ := exists_forall_weylForm_intertwiningMap_apply_eq f h
        rw [hc, weylForm_eq_zero_of_mem_gtLine m (fun e ↦ hne (congrArg Subtype.val e)) hx' hy',
          mul_zero]
      · exact weylForm_intertwiningMap_apply_eq_zero hm f h x' y'
    have hmem (R : {P : GTPattern (n + 1) // P.topWeight = l}) :
        R.1.truncate.topWeight ∈ interlacingWeights l := by
      have h := R.1.topWeight_truncate_mem_interlacingWeights
      rwa [R.2] at h
    obtain ⟨f, hf⟩ := exists_intertwiningMap_ne_zero_of_mem_interlacingWeights (hmem P)
    obtain ⟨h, hh⟩ := exists_intertwiningMap_ne_zero_of_mem_interlacingWeights (hmem Q)
    rw [gtLine_succ l P f hf] at hx
    rw [gtLine_succ l Q h hh] at hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    refine key f h _ _ (fun e ↦ hPQ (Subtype.ext ?_)) hx' hy'
    -- A pattern is determined by its top row and its truncation.
    have hP : P.1.topRow = l := by rw [← GTPattern.topWeight_coe, P.2]
    have hQ : Q.1.topRow = l := by rw [← GTPattern.topWeight_coe, Q.2]
    exact Subtype.mk.inj ((GTPattern.truncateEquiv (l : Fin (n + 1) → ℤ)).injective
      (a₁ := ⟨P.1, hP⟩) (a₂ := ⟨Q.1, hQ⟩) (Subtype.ext (by simpa using e)))

variable {n : ℕ} (l : DominantWeight n)

/-- Each Gelfand–Tsetlin line contains a vector of norm one for the contravariant form. -/
private theorem exists_mem_gtLine_weylForm_apply_self_eq_one
    (P : {P : GTPattern n // P.topWeight = l}) :
    ∃ v ∈ gtLine l P, weylForm n _ v v = 1 := by
  have := Module.nontrivial_of_finrank_eq_succ (finrank_gtLine l P)
  obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : gtLine l P)
  obtain ⟨r, hr, hrw⟩ := RCLike.pos_iff_exists_ofReal.mp
    (weylForm_apply_self_pos (fun h ↦ hw0 (Subtype.ext h) : w ≠ 0))
  have hne : ((√r : ℝ) : ℂ) ≠ 0 := mod_cast (Real.sqrt_pos.mpr hr).ne'
  have hsq : ((√r : ℝ) : ℂ) * (√r : ℝ) = (r : ℂ) := mod_cast Real.mul_self_sqrt hr.le
  refine ⟨(((√r : ℝ) : ℂ))⁻¹ • w, Submodule.smul_mem _ _ hw, ?_⟩
  have hr' : weylForm n _ w w = (r : ℂ) := hrw.symm
  simp only [map_smulₛₗ, LinearMap.smul_apply, hr', RingHom.id_apply, map_inv₀, smul_eq_mul,
    Complex.conj_ofReal, ← hsq]
  field_simp

/-- A choice of a vector of norm one in each Gelfand–Tsetlin line. -/
private noncomputable def gtVector (P : {P : GTPattern n // P.topWeight = l}) :
    (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule :=
  (exists_mem_gtLine_weylForm_apply_self_eq_one l P).choose

private theorem gtVector_mem (P : {P : GTPattern n // P.topWeight = l}) :
    gtVector l P ∈ gtLine l P :=
  (exists_mem_gtLine_weylForm_apply_self_eq_one l P).choose_spec.1

private theorem weylForm_gtVector (P : {P : GTPattern n // P.topWeight = l}) :
    weylForm n _ (gtVector l P) (gtVector l P) = 1 :=
  (exists_mem_gtLine_weylForm_apply_self_eq_one l P).choose_spec.2

private theorem gtVector_ne_zero (P : {P : GTPattern n // P.topWeight = l}) :
    gtVector l P ≠ 0 := fun h ↦ by
  have := weylForm_gtVector l P
  simp [h] at this

/-- A nonzero vector of a Gelfand–Tsetlin line spans it. -/
theorem span_singleton_eq_gtLine {P : {P : GTPattern n // P.topWeight = l}}
    {v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule} (hv : v ∈ gtLine l P) (hv0 : v ≠ 0) :
    Submodule.span ℂ {v} = gtLine l P := by
  refine le_antisymm ((Submodule.span_singleton_le_iff_mem _ _).mpr hv) fun w hw ↦ ?_
  -- Fix the additive groups of the carrier and the line before applying the one-dimensional lemma.
  let _ : AddCommGroup (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule := inferInstance
  let _ : AddCommGroup (gtLine l P) := inferInstance
  have hv0' : (⟨v, hv⟩ : gtLine l P) ≠ 0 := fun h ↦ hv0 (Subtype.ext_iff.mp h)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (finrank_gtLine l P) hv0'
    (⟨w, hw⟩ : gtLine l P)
  exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext_iff.mp hc⟩

open scoped Classical in
private theorem linearIndependent_gtVector : LinearIndependent ℂ (gtVector l) :=
  (isInternal_gtLine l).submodule_iSupIndep.linearIndependent (R := ℂ)
    (N := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule) _ (gtVector_mem l)
    (gtVector_ne_zero l)

open scoped Classical in
private theorem top_le_span_range_gtVector : ⊤ ≤ Submodule.span ℂ (Set.range (gtVector l)) := by
  rw [← (isInternal_gtLine l).submodule_iSup_eq_top]
  refine iSup_le fun P ↦ ?_
  rw [← span_singleton_eq_gtLine l (gtVector_mem l P) (gtVector_ne_zero l P)]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self P))

/-- **The Gelfand–Tsetlin basis** of the rational Weyl module `V_λ` of `GL n ℂ`, indexed by the
patterns with top weight `λ`. Its vector at `P` generates the Gelfand–Tsetlin line of `P`
(`TauCeti.gtBasis_mem_gtLine`), and the basis is orthonormal for the contravariant form
(`TauCeti.weylForm_gtBasis_self`, `TauCeti.weylForm_gtBasis_of_ne`). These properties determine each
vector up to a complex scalar of absolute value one
(`TauCeti.exists_norm_eq_one_and_eq_smul_gtBasis`). -/
noncomputable def gtBasis : Basis {P : GTPattern n // P.topWeight = l} ℂ
    (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule :=
  Basis.mk (linearIndependent_gtVector l) (top_le_span_range_gtVector l)

private theorem gtBasis_apply (P : {P : GTPattern n // P.topWeight = l}) :
    gtBasis l P = gtVector l P :=
  Basis.mk_apply _ _ P

/-- Each vector of the Gelfand–Tsetlin basis lies in the line of its pattern. -/
theorem gtBasis_mem_gtLine (P : {P : GTPattern n // P.topWeight = l}) :
    gtBasis l P ∈ gtLine l P := by
  rw [gtBasis_apply]
  exact gtVector_mem l P

/-- Each vector of the Gelfand–Tsetlin basis generates the line of its pattern. -/
theorem span_singleton_gtBasis (P : {P : GTPattern n // P.topWeight = l}) :
    Submodule.span ℂ {gtBasis l P} = gtLine l P :=
  span_singleton_eq_gtLine l (gtBasis_mem_gtLine l P) ((gtBasis l).ne_zero P)

/-- The vectors of the Gelfand–Tsetlin basis have norm one for the contravariant form. -/
@[simp]
theorem weylForm_gtBasis_self (P : {P : GTPattern n // P.topWeight = l}) :
    weylForm n _ (gtBasis l P) (gtBasis l P) = 1 := by
  rw [gtBasis_apply]
  exact weylForm_gtVector l P

/-- Distinct vectors of the Gelfand–Tsetlin basis are orthogonal for the contravariant form. -/
theorem weylForm_gtBasis_of_ne {P Q : {P : GTPattern n // P.topWeight = l}} (h : P ≠ Q) :
    weylForm n _ (gtBasis l P) (gtBasis l Q) = 0 :=
  weylForm_eq_zero_of_mem_gtLine l h (gtBasis_mem_gtLine l P) (gtBasis_mem_gtLine l Q)

/-- The coordinates in the Gelfand–Tsetlin basis are computed by the contravariant form. -/
theorem gtBasis_repr_apply (x : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
    (P : {P : GTPattern n // P.topWeight = l}) :
    (gtBasis l).repr x P = weylForm n _ (gtBasis l P) x := by
  have h : (Finsupp.lapply P) ∘ₗ ((gtBasis l).repr : _ →ₗ[ℂ] _) =
      weylForm n _ (gtBasis l P) := by
    refine (gtBasis l).ext fun Q ↦ ?_
    by_cases hQ : Q = P
    · simp [hQ]
    · simp [hQ, weylForm_gtBasis_of_ne l (Ne.symm hQ)]
  exact LinearMap.congr_fun h x

/-- **Uniqueness of the Gelfand–Tsetlin basis up to phases.** A vector of norm one in the line of
`P` is the vector of the Gelfand–Tsetlin basis at `P`, up to a scalar of absolute value one. -/
theorem exists_norm_eq_one_and_eq_smul_gtBasis {P : {P : GTPattern n // P.topWeight = l}}
    {v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule} (hv : v ∈ gtLine l P)
    (hvv : weylForm n _ v v = 1) : ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • gtBasis l P := by
  rw [← span_singleton_gtBasis] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨c, ?_, rfl⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, weylForm_gtBasis_self, RingHom.id_apply, smul_eq_mul,
    mul_one, Complex.mul_conj'] at hvv
  have h : ‖c‖ ^ 2 = 1 := by exact_mod_cast hvv
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).mp h

/-- **The Gelfand–Tsetlin generators are diagonal in the Gelfand–Tsetlin basis.** The generator of
degree `r` at level `k ≤ n` acts on the basis vector of a pattern `P` by the scalar
`gelfandEigenvalue` of the row of `P` of length `k`. -/
theorem lift_differential_gelfandTsetlinGenerator_apply_gtBasis
    (P : {P : GTPattern n // P.topWeight = l}) {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
        (gelfandTsetlinGenerator ℂ hk r) (gtBasis l P) =
      gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r • gtBasis l P :=
  lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine l P hk r (gtBasis_mem_gtLine l P)

end TauCeti
