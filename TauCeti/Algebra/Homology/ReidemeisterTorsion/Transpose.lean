/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Alternating.Append
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Determinant.Dual
import TauCeti.LinearAlgebra.Matrix.Dual
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# The torsion of the transpose of a based two-periodic complex

Let `C` and `D` be two-periodic complexes of vector spaces over a field `F`, with ordered bases
`c i` and `e i` of the same lengths `n i`, such that the matrix of each differential of `D` is
the transpose of the matrix of the other differential of `C`:

`[D.d 0 1]_e = ([C.d 1 0]_c)ᵀ`,  `[D.d 1 0]_e = ([C.d 0 1]_c)ᵀ`.

This is how the based dual complex looks in coordinates: if `D` is the dual of `C`, with the
dual bases `e i` of the `c i` and each differential of `D` the transpose of the differential of
`C` in the opposite direction, then the matrices satisfy these equations. In a two-periodic
complex the transposes run again from even to odd and from odd to even degree, so the dual is
again a two-periodic complex, with no parity shift.

The torsion of the dual complex is the inverse of the torsion of `C`
(`HomologicalComplex.parityTorsion_eq_inv_of_toMatrix_eq_transpose`):

`τ(D, e) = τ(C, c)⁻¹`.

Both sides vanish when `C` is not acyclic, because `D` is acyclic exactly when `C` is
(`HomologicalComplex.acyclic_iff_of_toMatrix_eq_transpose`): transposition preserves the rank of
each differential. When `C` is acyclic, choose bases `b₀`, `b₁` of its boundaries and lifts `s₀`,
`s₁`, so that `u₀ = (b₀, s₀)` and `u₁ = (b₁, s₁)` are bases of `C₀` and `C₁` in which the
differentials send `s₀ ↦ b₁` and `s₁ ↦ b₀` and kill the boundaries. In the dual bases
`u₀^* = (β₀, σ₀)` and `u₁^* = (β₁, σ₁)` of `D₀` and `D₁` the transposed differentials send
`β₁ ↦ σ₀` and `β₀ ↦ σ₁` and kill `σ₀` and `σ₁`. So the `σ` span the boundaries of `D`, the `β`
are lifts, and the brackets of `D` are those of the reordered dual bases `(σⱼ, βⱼ)`. The
determinant of a dual basis is the inverse of that of the basis, and moving the block `σⱼ` in
front costs the same sign `(-1) ^ (dim B₀ · dim B₁)` in both degrees; these signs cancel in the
torsion, which is the ratio of the two brackets.

For instance the complex `F → F` given by multiplication by `a ≠ 0` from the odd to the even
degree has torsion `a⁻¹`, and its dual, multiplication by `a` from the even to the odd degree,
has torsion `a`.

A Floer complex can be read through its dual complex, for instance when the roles of the input
and output ends of the trajectories are exchanged; this formula is the effect of that
dualization on the torsion of a based parity complex.

## Main results

* `HomologicalComplex.acyclic_iff_of_toMatrix_eq_transpose`: a based two-periodic complex whose
  differentials have the transposed matrices of those of `C` is acyclic exactly when `C` is.
* `HomologicalComplex.parityTorsion_eq_inv_of_toMatrix_eq_transpose`: its torsion is the
  inverse of the torsion of `C`.

## References

* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
* V. Turaev, *Introduction to combinatorial torsions*, Birkhäuser 2001, §1.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), §2.
-/

public section

noncomputable section

open CategoryTheory Module
open scoped Matrix

namespace HomologicalComplex

variable {F : Type*} [Field F]

section LinearAlgebra

variable {ι ι' V V' W W' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module F W]
  [AddCommGroup W'] [Module F W']

/-- The identification of `W` with the dual of `V` sending the basis `e` to the dual basis of
`c`. -/
private abbrev pairingEquiv (c : Basis ι F V) (e : Basis ι F W) : W ≃ₗ[F] Dual F V :=
  e.equiv c.dualBasis (Equiv.refl ι)

variable {Ψ : W ≃ₗ[F] Dual F V} {Ψ' : W' ≃ₗ[F] Dual F V'} {f : V →ₗ[F] V'} {g : W' →ₗ[F] W}
  {p q r : ℕ} (U : Basis (Fin (p + q)) F V) (U' : Basis (Fin (q + r)) F V')

/-- Let `g` be the transpose of `f` under identifications `Ψ`, `Ψ'` with duals. If `f` kills the
first `p` vectors of a basis `U` and sends its last `q` vectors to the first `q` vectors of a
basis `U'`, then `g` sends the first `q` vectors of the dual basis of `U'` to the last `q` vectors
of the dual basis of `U`. -/
private theorem map_dualBasis_castAdd (hfg : ∀ y, Ψ (g y) = (Ψ' y).comp f)
    (h₁ : ∀ a, f (U (Fin.castAdd q a)) = 0)
    (h₂ : ∀ a, f (U (Fin.natAdd p a)) = U' (Fin.castAdd r a)) (a : Fin q) :
    g ((U'.dualBasis.map Ψ'.symm) (Fin.castAdd r a)) =
      (U.dualBasis.map Ψ.symm) (Fin.natAdd p a) := by
  refine Ψ.injective (U.ext fun k ↦ ?_)
  induction k using Fin.addCases with
  | left k => simp [hfg, h₁, Finsupp.single_apply, Fin.ext_iff]; omega
  | right k => simp [hfg, h₂, Finsupp.single_apply, Fin.ext_iff]

/-- In the situation of `map_dualBasis_castAdd`, the transpose `g` kills the last `r` vectors of
the dual basis of `U'`. -/
private theorem map_dualBasis_natAdd (hfg : ∀ y, Ψ (g y) = (Ψ' y).comp f)
    (h₁ : ∀ a, f (U (Fin.castAdd q a)) = 0)
    (h₂ : ∀ a, f (U (Fin.natAdd p a)) = U' (Fin.castAdd r a)) (a : Fin r) :
    g ((U'.dualBasis.map Ψ'.symm) (Fin.natAdd q a)) = 0 := by
  refine Ψ.injective (U.ext fun k ↦ ?_)
  induction k using Fin.addCases with
  | left k => simp [hfg, h₁]
  | right k => simp [hfg, h₂, Finsupp.single_apply, Fin.ext_iff]; omega

variable {U U'}

/-- If a linear map `g` sends the first `q` vectors of a basis `X` to the last `q` vectors of a
basis `Y` and kills the last `r` vectors of `X`, its image is spanned by those `q` vectors of
`Y`. -/
private theorem range_eq_span (X : Basis (Fin (q + r)) F W') (Y : Basis (Fin (p + q)) F W)
    (h₁ : ∀ a, g (X (Fin.castAdd r a)) = Y (Fin.natAdd p a))
    (h₂ : ∀ a, g (X (Fin.natAdd q a)) = 0) :
    Submodule.span F (Set.range (Y ∘ Fin.natAdd p)) = LinearMap.range g := by
  rw [X.range_eq_span_comp g]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨Fin.castAdd r a, h₁ a⟩
  · rintro _ ⟨m, rfl⟩
    induction m using Fin.addCases with
    | left a => rw [Function.comp_apply, h₁ a]; exact Submodule.subset_span ⟨a, rfl⟩
    | right a => rw [Function.comp_apply, h₂ a]; exact Submodule.zero_mem _

/-- The determinant, in a basis `e` identified with the dual basis of `c`, of the dual basis `Y`
of a basis `U` of length `p + q`, with its last `q` vectors moved in front of its first `p`, is
`(-1) ^ (p * q)` times the inverse of the determinant of `U` in `c`. -/
private theorem det_append_dualBasis {N : ℕ} (c : Basis (Fin N) F V) (e : Basis (Fin N) F W)
    (U : Basis (Fin (p + q)) F V) {Y : Basis (Fin (p + q)) F W}
    (hY : Y = U.dualBasis.map (pairingEquiv c e).symm) (hN : N = q + p) :
    e.det (Fin.append (fun a ↦ Y (Fin.natAdd p a)) (fun a ↦ Y (Fin.castAdd q a)) ∘ Fin.cast hN) =
      (-1) ^ (p * q) * (c.det (U ∘ Fin.cast (hN.trans (add_comm q p))))⁻¹ := by
  set φ : Fin N ≃ Fin (p + q) := finCongr (hN.trans (add_comm q p))
  -- Move the block of the last `q` dual vectors behind the first `p`.
  have hswap : e.det (Fin.append (fun a ↦ Y (Fin.natAdd p a)) (fun a ↦ Y (Fin.castAdd q a)) ∘
      Fin.cast hN) = (-1) ^ (p * q) * e.det (Y ∘ φ) := by
    have h := (e.reindex φ).det.map_append_comm (fun a ↦ Y (Fin.castAdd q a))
      (fun a ↦ Y (Fin.natAdd p a))
    have hcast : Fin.cast (add_comm p q) ∘ φ = Fin.cast hN := funext fun k ↦ Fin.ext rfl
    rw [Basis.det_reindex, Basis.det_reindex, Function.comp_assoc, hcast,
      Fin.append_castAdd_natAdd] at h
    rw [h, Units.smul_def]
    simp
  -- The basis `e` is the image of the dual basis of `c`, so the determinant of `Y ∘ φ` in `e` is
  -- that of the dual basis of `U ∘ φ` in the dual basis of `c`, the inverse of `[U ∘ φ / c]`.
  have he : e = c.dualBasis.map (pairingEquiv c e).symm :=
    Basis.eq_of_apply_eq fun k ↦ by simp
  have hYφ : e.det (Y ∘ φ) = c.dualBasis.det (U.dualBasis ∘ φ) := by
    conv_lhs => rw [he]
    rw [Basis.det_map]
    congr 1
    funext k
    simp only [hY, Function.comp_apply, Basis.map_apply, LinearEquiv.symm_symm,
      LinearEquiv.apply_symm_apply]
  have hdet : c.dualBasis.det (U.dualBasis ∘ φ) * c.det (U ∘ φ) = 1 := by
    have hU : ⇑(U.reindex φ.symm).dualBasis = U.dualBasis ∘ φ := by
      ext k v
      simp
    simpa [hU] using c.dualBasis_det_dualBasis_mul_det (U.reindex φ.symm)
  rw [hswap, hYφ, eq_inv_of_mul_eq_one_left hdet]
  simp [φ, Function.comp_def]

end LinearAlgebra

variable {C D : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
  {c : ∀ i, Basis (Fin (n i)) F (C.X i)} {e : ∀ i, Basis (Fin (n i)) F (D.X i)}

/-- At a degree `j` of a two-periodic complex with neighbouring degree `k`, if the spaces of
`C` and `D` in degree `j` have bases of the same length and the differentials of `D` into and out
of `j` have ranges of the dimensions of those of `C` out of and into `j`, then `D` is exact at `j`
exactly when `C` is. -/
private theorem exactAt_iff_of_finrank_range_eq {j k : ZMod 2} {m : ℕ}
    (cj : Basis (Fin m) F (C.X j)) (ej : Basis (Fin m) F (D.X j))
    (hjk : (ComplexShape.up (ZMod 2)).Rel j k) (hkj : (ComplexShape.up (ZMod 2)).Rel k j)
    (hin : finrank F (LinearMap.range (D.d k j).hom) =
      finrank F (LinearMap.range (C.d j k).hom))
    (hout : finrank F (LinearMap.range (D.d j k).hom) =
      finrank F (LinearMap.range (C.d k j).hom)) :
    D.ExactAt j ↔ C.ExactAt j := by
  have : Module.Finite F (C.X j) := .of_basis cj
  have : Module.Finite F (D.X j) := .of_basis ej
  rw [exactAt_iff_finrank_add_finrank D (ComplexShape.prev_eq' _ hkj)
      (ComplexShape.next_eq' _ hjk),
    exactAt_iff_finrank_add_finrank C (ComplexShape.prev_eq' _ hkj)
      (ComplexShape.next_eq' _ hjk),
    hin, hout, finrank_eq_card_basis cj, finrank_eq_card_basis ej, add_comm]

/-- A based two-periodic complex `D` whose differentials have, in the bases `e`, the transposes
of the matrices of the differentials of `C` in the bases `c` is acyclic exactly when `C` is. -/
theorem acyclic_iff_of_toMatrix_eq_transpose
    (h₀₁ : LinearMap.toMatrix (e 0) (e 1) (D.d 0 1).hom =
      (LinearMap.toMatrix (c 1) (c 0) (C.d 1 0).hom)ᵀ)
    (h₁₀ : LinearMap.toMatrix (e 1) (e 0) (D.d 1 0).hom =
      (LinearMap.toMatrix (c 0) (c 1) (C.d 0 1).hom)ᵀ) :
    D.Acyclic ↔ C.Acyclic := by
  -- Transposition preserves the rank of the matrices of the differentials.
  have hrk₀₁ := LinearMap.finrank_range_eq_of_toMatrix_eq_transpose h₀₁
  have hrk₁₀ := LinearMap.finrank_range_eq_of_toMatrix_eq_transpose h₁₀
  have hr₁₀ : (ComplexShape.up (ZMod 2)).Rel 1 0 := CharTwo.add_self_eq_zero 1
  have hr₀₁ : (ComplexShape.up (ZMod 2)).Rel 0 1 := zero_add 1
  refine forall_congr' fun j ↦ ?_
  fin_cases j
  exacts [exactAt_iff_of_finrank_range_eq (c 0) (e 0) hr₀₁ hr₁₀ hrk₁₀ hrk₀₁,
    exactAt_iff_of_finrank_range_eq (c 1) (e 1) hr₁₀ hr₀₁ hrk₀₁ hrk₁₀]

/-- An acyclic based two-periodic complex `C` has bases `U₀` of `C₀` and `U₁` of `C₁`, made of
bases of the boundaries followed by lifts, in which the torsion is the ratio of the
determinants of `U₁` and `U₀` and the differentials kill the boundaries and send the lifts to
the boundary bases. -/
private theorem exists_adaptedBasis (hC : C.Acyclic) :
    ∃ (p q : ℕ) (U₀ : Basis (Fin (p + q)) F (C.X 0)) (U₁ : Basis (Fin (q + p)) F (C.X 1))
      (hn₀ : n 0 = p + q) (hn₁ : n 1 = q + p),
      C.parityTorsion c = (c 1).det (U₁ ∘ Fin.cast hn₁) * ((c 0).det (U₀ ∘ Fin.cast hn₀))⁻¹ ∧
      (∀ a, (C.d 0 1).hom (U₀ (Fin.castAdd q a)) = 0) ∧
      (∀ a, (C.d 0 1).hom (U₀ (Fin.natAdd p a)) = U₁ (Fin.castAdd p a)) ∧
      (∀ a, (C.d 1 0).hom (U₁ (Fin.castAdd p a)) = 0) ∧
      (∀ a, (C.d 1 0).hom (U₁ (Fin.natAdd q a)) = U₀ (Fin.castAdd q a)) := by
  have hr₁₀ : (ComplexShape.up (ZMod 2)).Rel 1 0 := CharTwo.add_self_eq_zero 1
  have hr₀₁ : (ComplexShape.up (ZMod 2)).Rel 0 1 := zero_add 1
  set b₀ := chosenBoundaryBasis C c 1 0
  set b₁ := chosenBoundaryBasis C c 0 1
  have hs₀ := chosenBoundaryLift_spec C c 0 1
  have hs₁ := chosenBoundaryLift_spec C c 1 0
  -- The bases `U₀ = (b₀, s₀)` of `C₀` and `U₁ = (b₁, s₁)` of `C₁`.
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Basis (Fin (_ + _)) F (C.X 0),
      ⇑U₀ = Fin.append (fun l ↦ (b₀ l : C.X 0)) (chosenBoundaryLift C c 0 1) :=
    ⟨_, Basis.coe_reindex_ofExactLift (Submodule.injective_subtype _)
      (exact_subtype_rangeRestrict (ComplexShape.prev_eq' _ hr₁₀) (ComplexShape.next_eq' _ hr₀₁)
        (hC 0)) b₀ b₁ _ fun l ↦ Subtype.ext (hs₀ l)⟩
  obtain ⟨U₁, hU₁⟩ : ∃ U₁ : Basis (Fin (_ + _)) F (C.X 1),
      ⇑U₁ = Fin.append (fun l ↦ (b₁ l : C.X 1)) (chosenBoundaryLift C c 1 0) :=
    ⟨_, Basis.coe_reindex_ofExactLift (Submodule.injective_subtype _)
      (exact_subtype_rangeRestrict (ComplexShape.prev_eq' _ hr₀₁) (ComplexShape.next_eq' _ hr₁₀)
        (hC 1)) b₁ b₀ _ fun l ↦ Subtype.ext (hs₁ l)⟩
  have hn₀ := eq_add_of_exactAt c (ComplexShape.prev_eq' _ hr₁₀) (ComplexShape.next_eq' _ hr₀₁)
    (hC 0) b₀ b₁
  have hn₁ := eq_add_of_exactAt c (ComplexShape.prev_eq' _ hr₀₁) (ComplexShape.next_eq' _ hr₁₀)
    (hC 1) b₁ b₀
  refine ⟨_, _, U₀, U₁, hn₀, hn₁, ?_, fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_, fun a ↦ ?_⟩
  · rw [parityTorsion_eq hC b₀ b₁ _ hs₀ _ hs₁, torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hn₁,
      torsionBracket_eq_det_append _ _ _ _ _ _ _ _ hn₀, hU₀, hU₁]
  · obtain ⟨x, hx⟩ := (b₀ a).property
    rw [hU₀, Fin.append_left, ← hx]
    exact d_comp_d_apply C _ _ _ x
  · rw [hU₀, hU₁, Fin.append_right, Fin.append_left, hs₀]
  · obtain ⟨x, hx⟩ := (b₁ a).property
    rw [hU₁, Fin.append_left, ← hx]
    exact d_comp_d_apply C _ _ _ x
  · rw [hU₀, hU₁, Fin.append_right, Fin.append_left, hs₁]

/-- The torsion of the dual complex of an acyclic based two-periodic complex `C`, computed in
bases `U₀`, `U₁` of `C` as in `exists_adaptedBasis`. -/
private theorem parityTorsion_eq_inv_det_mul_inv_det
    (h₀₁ : LinearMap.toMatrix (e 0) (e 1) (D.d 0 1).hom =
      (LinearMap.toMatrix (c 1) (c 0) (C.d 1 0).hom)ᵀ)
    (h₁₀ : LinearMap.toMatrix (e 1) (e 0) (D.d 1 0).hom =
      (LinearMap.toMatrix (c 0) (c 1) (C.d 0 1).hom)ᵀ)
    (hD : D.Acyclic) {p q : ℕ} (U₀ : Basis (Fin (p + q)) F (C.X 0))
    (U₁ : Basis (Fin (q + p)) F (C.X 1)) (hn₀ : n 0 = p + q) (hn₁ : n 1 = q + p)
    (hz₀ : ∀ a, (C.d 0 1).hom (U₀ (Fin.castAdd q a)) = 0)
    (hm₀ : ∀ a, (C.d 0 1).hom (U₀ (Fin.natAdd p a)) = U₁ (Fin.castAdd p a))
    (hz₁ : ∀ a, (C.d 1 0).hom (U₁ (Fin.castAdd p a)) = 0)
    (hm₁ : ∀ a, (C.d 1 0).hom (U₁ (Fin.natAdd q a)) = U₀ (Fin.castAdd q a)) :
    D.parityTorsion e =
      ((c 1).det (U₁ ∘ Fin.cast hn₁) * ((c 0).det (U₀ ∘ Fin.cast hn₀))⁻¹)⁻¹ := by
  -- The dual bases `W₀ = (β₀, σ₀)` of `D₀` and `W₁ = (β₁, σ₁)` of `D₁`: the differentials of `D`
  -- kill the `σ` and send `β₁ ↦ σ₀` and `β₀ ↦ σ₁`.
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Basis (Fin (p + q)) F (D.X 0),
      W₀ = U₀.dualBasis.map (pairingEquiv (c 0) (e 0)).symm := ⟨_, rfl⟩
  obtain ⟨W₁, hW₁⟩ : ∃ W₁ : Basis (Fin (q + p)) F (D.X 1),
      W₁ = U₁.dualBasis.map (pairingEquiv (c 1) (e 1)).symm := ⟨_, rfl⟩
  have hΨ₁₀ := LinearMap.congr_fun
    ((LinearMap.toMatrix_eq_transpose_iff (c 0) (c 1) (e 0) (e 1)).1 h₁₀)
  have hΨ₀₁ := LinearMap.congr_fun
    ((LinearMap.toMatrix_eq_transpose_iff (c 1) (c 0) (e 1) (e 0)).1 h₀₁)
  have hβ₁ (a : Fin q) : (D.d 1 0).hom (W₁ (Fin.castAdd p a)) = W₀ (Fin.natAdd p a) := by
    rw [hW₀, hW₁]; exact map_dualBasis_castAdd U₀ U₁ hΨ₁₀ hz₀ hm₀ a
  have hσ₁ (a : Fin p) : (D.d 1 0).hom (W₁ (Fin.natAdd q a)) = 0 := by
    rw [hW₁]; exact map_dualBasis_natAdd (Ψ := pairingEquiv (c 0) (e 0)) U₀ U₁ hΨ₁₀ hz₀ hm₀ a
  have hβ₀ (a : Fin p) : (D.d 0 1).hom (W₀ (Fin.castAdd q a)) = W₁ (Fin.natAdd q a) := by
    rw [hW₀, hW₁]; exact map_dualBasis_castAdd U₁ U₀ hΨ₀₁ hz₁ hm₁ a
  have hσ₀ (a : Fin q) : (D.d 0 1).hom (W₀ (Fin.natAdd p a)) = 0 := by
    rw [hW₀]; exact map_dualBasis_natAdd (Ψ := pairingEquiv (c 1) (e 1)) U₁ U₀ hΨ₀₁ hz₁ hm₁ a
  -- So the `σ` are bases of the boundaries of `D`, with lifts the `β`, and the brackets of `D` are
  -- the determinants of the reordered dual bases `(σⱼ, βⱼ)`.
  rw [parityTorsion_eq hD
      (Basis.ofSpanEq (W₀.linearIndependent.comp _ (Fin.natAdd_injective q p))
        (range_eq_span W₁ W₀ hβ₁ hσ₁))
      (Basis.ofSpanEq (W₁.linearIndependent.comp _ (Fin.natAdd_injective p q))
        (range_eq_span W₀ W₁ hβ₀ hσ₀))
      (fun a ↦ W₀ (Fin.castAdd q a)) (fun a ↦ by rw [Basis.coe_ofSpanEq, Function.comp_apply, hβ₀])
      (fun a ↦ W₁ (Fin.castAdd p a)) (fun a ↦ by rw [Basis.coe_ofSpanEq, Function.comp_apply, hβ₁]),
    torsionBracket_eq_det_append _ _ _ _ _ _ _ _ (hn₁.trans (add_comm q p)),
    torsionBracket_eq_det_append _ _ _ _ _ _ _ _ (hn₀.trans (add_comm p q))]
  simp only [Basis.coe_ofSpanEq, Function.comp_apply]
  rw [det_append_dualBasis (c 1) (e 1) U₁ hW₁, det_append_dualBasis (c 0) (e 0) U₀ hW₀,
    mul_comm q p]
  have hpow : ((-1 : F) ^ (p * q)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  field_simp

/-- **The torsion of the dual complex.** If the differentials of a based two-periodic complex
`(D, e)` have the transposes of the matrices of the differentials of `(C, c)` in the opposite
directions, then the torsion of `D` is the inverse of the torsion of `C`. Both sides vanish when
`C` is not acyclic. -/
theorem parityTorsion_eq_inv_of_toMatrix_eq_transpose
    (h₀₁ : LinearMap.toMatrix (e 0) (e 1) (D.d 0 1).hom =
      (LinearMap.toMatrix (c 1) (c 0) (C.d 1 0).hom)ᵀ)
    (h₁₀ : LinearMap.toMatrix (e 1) (e 0) (D.d 1 0).hom =
      (LinearMap.toMatrix (c 0) (c 1) (C.d 0 1).hom)ᵀ) :
    D.parityTorsion e = (C.parityTorsion c)⁻¹ := by
  by_cases hC : C.Acyclic
  swap
  · have hD : ¬D.Acyclic := (acyclic_iff_of_toMatrix_eq_transpose h₀₁ h₁₀).not.2 hC
    simp [parityTorsion_of_not_acyclic _ _ hC, parityTorsion_of_not_acyclic _ _ hD]
  obtain ⟨p, q, U₀, U₁, hn₀, hn₁, hτ, hz₀, hm₀, hz₁, hm₁⟩ := exists_adaptedBasis (c := c) hC
  rw [hτ]
  exact parityTorsion_eq_inv_det_mul_inv_det h₀₁ h₁₀
    ((acyclic_iff_of_toMatrix_eq_transpose h₀₁ h₁₀).2 hC) U₀ U₁ hn₀ hn₁ hz₀ hm₀ hz₁ hm₁

end HomologicalComplex
