/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Stack.Sectors
public import TauCeti.Geometry.RealAlgebraic.IrreducibleBasis
public import TauCeti.Geometry.RealAlgebraic.OrderInvariant
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Nonsingular McCallum lifting

Nonvanishing leading coefficients, discriminants, and pairwise resultants give a common
delineation of a finite polynomial family: degrees are preserved, every fiber is separable,
and distinct members have no common roots. This uses the smaller projection data directly,
without adding derivatives or subresultants to the projection.

For an irreducible basis over a connected real analytic submanifold, the resulting stack
consists of analytic submanifolds. Each basis polynomial has ambient order one on its root
sections and zero elsewhere. Constant ambient order of the input contents therefore makes
every original input order-invariant, and hence sign-invariant, on every stack cell. Contents
may vanish, so some original inputs may be nullified even though no basis member is nullified.
The empty basis and zero inputs are included.

These statements concern the nonsingular case. Discriminants or pairwise resultants that
vanish on the base require additional analytic preparation.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268, Sections 2–3.
-/

public section

open Function MvPolynomial Polynomial Set

namespace TauCeti

variable {R X : Type*} [CommRing R] [TopologicalSpace X] [PreconnectedSpace X]
  {B : Finset R[X]}

/-- A finite family delineates a preconnected base when its leading coefficients,
discriminants, and pairwise resultants specialize to nonzero values everywhere.
Only coefficient continuity is required. -/
theorem nonempty_delineation_of_leadingCoeff_discr_resultant_ne_zero
    (φ : X → R →+* ℝ) (hc : ∀ b ∈ B, ∀ j, Continuous fun x ↦ φ x (b.coeff j))
    (hlc : ∀ b ∈ B, ∀ x, φ x b.leadingCoeff ≠ 0)
    (hdiscr : ∀ b ∈ B, ∀ x, φ x b.discr ≠ 0)
    (hres : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → ∀ x, φ x (resultant b c) ≠ 0) :
    Nonempty (Delineation fun (b : B) x ↦ b.1.map (φ x)) := by
  classical
  have hdeg (b : B) (x : X) : (b.1.map (φ x)).natDegree = b.1.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ (hlc _ b.2 x)
  have hs (b : B) (x : X) : (b.1.map (φ x)).Separable :=
    (b.1.separable_map_iff_map_discr_ne_zero (φ x) (hlc _ b.2 x)).mpr (hdiscr _ b.2 x)
  have hn (b : B) (x : X) : b.1.map (φ x) ≠ 0 := (hs b x).ne_zero
  have hcop (b c : B) (hne : b ≠ c) (x : X) :
      IsCoprime (b.1.map (φ x)) (c.1.map (φ x)) := by
    have hr : resultant (b.1.map (φ x)) (c.1.map (φ x)) ≠ 0 := by
      rw [hdeg b x, hdeg c x, resultant_map_map]
      exact hres _ b.2 _ c.2 (Subtype.coe_ne_coe.mpr hne) x
    exact not_not.mp fun h ↦ hr (resultant_eq_zero_iff.mpr ⟨Or.inl (hn b x), h⟩)
  refine nonempty_delineation (fun b j ↦ by simpa only [Polynomial.coeff_map] using hc _ b.2 j)
    (fun b ↦ Or.inr (hn b)) (fun b x y ↦ (hdeg b x).trans (hdeg b y).symm)
    (fun b x y ↦ ?_) (fun b c hne x y ↦ ?_)
  · have hcard (x : X) : ((b.1.map (φ x)).aroots ℂ).toFinset.card = b.1.natDegree := by
      rw [aroots, Multiset.toFinset_card_of_nodup (nodup_roots (hs b x).map),
        ← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_map, hdeg b x]
    exact (hcard x).trans (hcard y).symm
  · exact (natDegree_eq_zero_of_isUnit (EuclideanDomain.gcd_isUnit_iff.mpr (hcop b c hne x))).trans
      (natDegree_eq_zero_of_isUnit (EuclideanDomain.gcd_isUnit_iff.mpr (hcop b c hne y))).symm

end TauCeti

namespace Finset.IsIrreducibleBasis

variable {n d : ℕ} [NormalizedGCDMonoid (MvPolynomial (Fin n) ℝ)]
  {F B : Finset (Polynomial (MvPolynomial (Fin n) ℝ))}
  {S : Set (Fin n → ℝ)}

/-- Nonsingular lifting for an irreducible basis over a connected analytic submanifold.
The basis has a common delineation whose cells are analytic submanifolds, and every original
input has constant ambient order and sign on each cell. Only the contents need constant order
on the base; their values may vanish. -/
theorem exists_delineation_orderAt_eq_of_nonsingular (hB : F.IsIrreducibleBasis B)
    (hS : TauCeti.IsAnalyticSubmanifold d S) (hconn : IsPreconnected S)
    (hlc : ∀ b ∈ B, ∀ x ∈ S, MvPolynomial.eval x b.leadingCoeff ≠ 0)
    (hdiscr : ∀ b ∈ B, ∀ x ∈ S, MvPolynomial.eval x b.discr ≠ 0)
    (hres : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → ∀ x ∈ S,
      MvPolynomial.eval x (resultant b c) ≠ 0)
    (hcontent : ∀ f ∈ F, ∀ x ∈ S, ∀ y ∈ S, f.content.orderAt x = f.content.orderAt y) :
    ∃ D : TauCeti.Delineation fun (b : B) (x : S) ↦ b.1.map (MvPolynomial.eval x.1),
      ∀ E ∈ TauCeti.stackCells S D.root,
        (∃ e, (e = d ∨ e = d + 1) ∧ TauCeti.IsAnalyticSubmanifold e E) ∧
        ∀ f ∈ F,
          (∀ y ∈ E, ∀ y' ∈ E, ((finSuccEquiv ℝ n).symm f).orderAt y =
            ((finSuccEquiv ℝ n).symm f).orderAt y') ∧
          TauCeti.SignInvariant (fun y ↦ MvPolynomial.eval y ((finSuccEquiv ℝ n).symm f)) E := by
  classical
  have := isPreconnected_iff_preconnectedSpace.mp hconn
  obtain ⟨D⟩ := TauCeti.nonempty_delineation_of_leadingCoeff_discr_resultant_ne_zero
    (fun x : S ↦ MvPolynomial.eval x.1)
    (fun b _ j ↦ (MvPolynomial.continuous_eval (b.coeff j)).comp continuous_subtype_val)
    (fun b hb x ↦ hlc b hb x x.2) (fun b hb x ↦ hdiscr b hb x x.2)
    (fun b hb c hc hne x ↦ hres b hb c hc hne x x.2)
  -- Intrinsic analyticity of coefficients makes sections analytic; sectors are relatively open.
  have hcoeff (b : B) (j : ℕ) :
      TauCeti.AnalyticOnSubmanifold d
        (fun x ↦ (b.1.map (MvPolynomial.eval x)).coeff j) S :=
    hS.analyticOnSubmanifold_coeff_map_eval b.1 j
  refine ⟨D, fun E hE ↦ ⟨D.exists_isAnalyticSubmanifold_of_mem_stackCells hS hcoeff hE,
    fun f hf ↦ ?_⟩⟩
  -- Simple fiber zeros have ambient order one. Transfer these basis orders through factorization.
  have horder : ∀ y ∈ E, ∀ y' ∈ E, ((finSuccEquiv ℝ n).symm f).orderAt y =
      ((finSuccEquiv ℝ n).symm f).orderAt y' := by
    intro y hy y' hy'
    have hbase : ∀ z ∈ E, Fin.tail z ∈ S := by
      intro z hz
      rcases TauCeti.mem_stackCells.mp hE with ⟨i, rfl⟩ | ⟨j, rfl⟩ <;>
        exact (TauCeti.mem_image_cylinder.mp hz).1
    apply hB.orderAt_eq hf (hcontent f hf _ (hbase y hy) _ (hbase y' hy'))
    intro b hb
    have hsign : TauCeti.SignInvariant
        (fun z ↦ MvPolynomial.eval z ((finSuccEquiv ℝ n).symm b)) E := by
      apply D.signInvariant_eval₂_of_mem_stackCells (φ := RingHom.id ℝ) ?_ hE
      simpa using hb
    have hz : MvPolynomial.eval y ((finSuccEquiv ℝ n).symm b) = 0 ↔
        MvPolynomial.eval y' ((finSuccEquiv ℝ n).symm b) = 0 := by
      simpa only [sign_eq_zero_iff] using
        (congrArg (· = 0) (TauCeti.signInvariant_def.mp hsign y hy y' hy')).to_iff
    have hsep (z : Fin (n + 1) → ℝ) (hzS : Fin.tail z ∈ S) :
        (b.map (MvPolynomial.eval (Fin.tail z))).Separable := by
      exact (b.separable_map_iff_map_discr_ne_zero
        (MvPolynomial.eval (Fin.tail z)) (hlc b hb _ hzS)).mpr (hdiscr b hb _ hzS)
    rw [MvPolynomial.orderAt_eq_ite_of_separable_map_finSuccEquiv _ y
      (by simpa only [AlgEquiv.apply_symm_apply] using hsep y (hbase y hy)),
      MvPolynomial.orderAt_eq_ite_of_separable_map_finSuccEquiv _ y'
      (by simpa only [AlgEquiv.apply_symm_apply] using hsep y' (hbase y' hy')), hz]
  exact ⟨horder, (TauCeti.isConnected_of_mem_stackCells ⟨hS.nonempty, hconn⟩
    D.continuous_root D.strictMono_root hE).isPreconnected.signInvariant_eval_of_orderAt_eq horder⟩

end Finset.IsIrreducibleBasis
