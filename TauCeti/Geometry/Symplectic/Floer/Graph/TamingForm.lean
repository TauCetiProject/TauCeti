/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Symplectic.Floer.Graph.Manifold
import TauCeti.Geometry.Manifold.MFDeriv.Prod

/-!
# Gromov's taming form as a closed two-form

Let `ω` be a smooth two-form on a manifold `M` and let `K = K_s ds + K_t dt` be a Hamiltonian
perturbation whose components `K_s, K_t : (ℝ × ℝ) × M → ℝ` are smooth on the product. Gromov's
taming form `Ω_c = pr₂^* ω + dK + c ds ∧ dt` of the graph construction is given pointwise, on one
tangent space at a time, by `TauCeti.SmoothTwoForm.floerGraphForm`. This file assembles it into a
smooth two-form on the product manifold `(ℝ × ℝ) × M` and shows that it is closed exactly when `ω`
is. Compactness for unperturbed pseudoholomorphic curves applies to the graphs of Floer solutions
through a closed two-form taming Gromov's almost complex structure; this is that form.

* `TauCeti.SmoothTwoForm.floerGraphPrimitive K_s K_t c` is the one-form
  `λ_c = K_s ds + K_t dt + c s dt` on `(ℝ × ℝ) × M`
  (`TauCeti.SmoothTwoForm.floerGraphPrimitive_apply`), a primitive of `dK + c ds ∧ dt`
  (`TauCeti.SmoothTwoForm.mextDerivₗ_floerGraphPrimitive_apply`).
* `TauCeti.SmoothTwoForm.floerGraphTwoForm ω K_s K_t c` is the smooth two-form
  `Ω_c = pr₂^* ω + dλ_c` (`TauCeti.SmoothTwoForm.floerGraphTwoForm_def`). At every point it is
  Gromov's taming form (`TauCeti.SmoothTwoForm.eval₂_floerGraphTwoForm`), so the pointwise results
  of `TauCeti.Geometry.Symplectic.Floer.Graph.Manifold` apply to it: it tames Gromov's almost
  complex structure wherever `ω` tames `J` and `c + R_K > 0`, and on a graph it is the Floer energy
  density plus `c + R_K`.
* `Ω_c` differs from `pr₂^* ω` by an exact form, so it is closed exactly when `ω` is
  (`TauCeti.SmoothTwoForm.isClosed_floerGraphTwoForm_iff`).
* For a fibrewise nondegenerate `ω` and a smooth map `u : ℝ × ℝ → M`, the pullback of `Ω_c` along
  the graph of `u` takes the value `e(u) + c + R_K` on `(∂_s, ∂_t)`, where `e(u)` is the Floer
  energy density (`TauCeti.SmoothTwoForm.IsNondegenerate.eval₂_mpullback_graph_floerGraphTwoForm`).

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  graph construction and its taming form.
-/

public noncomputable section

open Function
open scoped Manifold

namespace TauCeti.SmoothTwoForm

open SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The domain coordinate `s` on `(ℝ × ℝ) × M`, as a smooth function. -/
private def coordS : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯ :=
  ⟨fun p ↦ p.1.1, contDiff_fst.contMDiff.comp contMDiff_fst⟩

/-- The domain coordinate `t` on `(ℝ × ℝ) × M`, as a smooth function. -/
private def coordT : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯ :=
  ⟨fun p ↦ p.1.2, contDiff_snd.contMDiff.comp contMDiff_fst⟩

/-- The derivative of the domain coordinate `s` reads the `s`-component of a tangent vector. -/
private theorem mvfderiv_coordS (p : (ℝ × ℝ) × M)
    (ζ : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    mvfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (coordS (I := I)) p ζ = ζ.1.1 := by
  refine (mvfderiv_comp_fst_apply (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) (fun z : ℝ × ℝ ↦ z.1) p ζ).trans ?_
  refine (mvfderiv_eq_fderiv_apply _ _ _).trans ?_
  rw [fderiv_fst]
  -- `ContinuousLinearMap.fst` reads the domain component of a product tangent vector.
  rfl

/-- The derivative of the domain coordinate `t` reads the `t`-component of a tangent vector. -/
private theorem mvfderiv_coordT (p : (ℝ × ℝ) × M)
    (ζ : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    mvfderiv (𝓘(ℝ, ℝ × ℝ).prod I) (coordT (I := I)) p ζ = ζ.1.2 := by
  refine (mvfderiv_comp_fst_apply (I := 𝓘(ℝ, ℝ × ℝ)) (J := I) (fun z : ℝ × ℝ ↦ z.2) p ζ).trans ?_
  refine (mvfderiv_eq_fderiv_apply _ _ _).trans ?_
  rw [fderiv_snd]
  -- `ContinuousLinearMap.snd` reads the domain component of a product tangent vector.
  rfl

/-- The derivative of a smooth function on `(ℝ × ℝ) × M` is the sum of its partial derivatives in
the domain and in the target. -/
private theorem mvfderiv_eq_fderiv_add_mvfderiv
    (K : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (p : (ℝ × ℝ) × M)
    (ζ : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    mvfderiv (𝓘(ℝ, ℝ × ℝ).prod I) K p ζ =
      fderiv ℝ (fun w ↦ K (w, p.2)) p.1 ζ.1 + mvfderiv I (fun x ↦ K (p.1, x)) p.2 ζ.2 := by
  rw [(K.contMDiff.mdifferentiableAt (by simp)).mvfderiv_prod_eq_add_apply]
  exact congrArg (· + _) (mvfderiv_eq_fderiv_apply _ _ _)

variable [IsManifold I (⊤ : ℕ∞) M]

/-- The one-form `λ_c = K_s ds + K_t dt + c s dt` on `(ℝ × ℝ) × M`, for smooth functions `K_s` and
`K_t` on the product: the Hamiltonian perturbation `K = K_s ds + K_t dt` plus `c s dt`. Its
exterior derivative is `dK + c ds ∧ dt`. -/
def floerGraphPrimitive (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (c : ℝ) :
    SmoothForm (𝓘(ℝ, ℝ × ℝ).prod I) ((ℝ × ℝ) × M) ℝ 1 :=
  funSMulₗ Ks (mextDerivₗ _ 0 (ofFunction coordS)) +
    funSMulₗ Kt (mextDerivₗ _ 0 (ofFunction coordT)) +
      c • funSMulₗ coordS (mextDerivₗ _ 0 (ofFunction coordT))

/-- The one-form `λ_c` sends a tangent vector `((a, b), v)` at `p` to
`K_s(p) a + (K_t(p) + c s) b`, where `s` is the first domain coordinate of `p`. -/
@[simp]
theorem floerGraphPrimitive_apply (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯)
    (c : ℝ) (p : (ℝ × ℝ) × M) (ζ : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    (floerGraphPrimitive Ks Kt c).val p ![ζ] = Ks p * ζ.1.1 + (Kt p + c * p.1.1) * ζ.1.2 := by
  simp only [floerGraphPrimitive, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply,
    Pi.smul_apply, coe_funSMulₗ, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul, mextDerivₗ_zero_apply, ofFunction_apply_zero]
  rw [mvfderiv_coordS, mvfderiv_coordT]
  simp only [coordS, ContMDiffMap.coeFn_mk]
  ring

/-- **Gromov's taming form** `Ω_c = pr₂^* ω + dK + c ds ∧ dt` on `(ℝ × ℝ) × M`, as a smooth
two-form, for a two-form `ω` on `M` and a Hamiltonian perturbation `K = K_s ds + K_t dt` with
components smooth on the product. It is `pr₂^* ω + dλ_c` for the one-form
`λ_c = K_s ds + K_t dt + c s dt` (`TauCeti.SmoothTwoForm.floerGraphPrimitive`), and at every point
it is the form `TauCeti.SmoothTwoForm.floerGraphForm`
(`TauCeti.SmoothTwoForm.eval₂_floerGraphTwoForm`). -/
def floerGraphTwoForm (ω : SmoothTwoForm I M)
    (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (c : ℝ) :
    SmoothTwoForm (𝓘(ℝ, ℝ × ℝ).prod I) ((ℝ × ℝ) × M) :=
  SmoothForm.mpullback Prod.snd contMDiff_snd ω + mextDerivₗ _ 1 (floerGraphPrimitive Ks Kt c)

/-- Gromov's taming form is the pullback of `ω` plus the exterior derivative of `λ_c`. -/
theorem floerGraphTwoForm_def (ω : SmoothTwoForm I M)
    (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (c : ℝ) :
    ω.floerGraphTwoForm Ks Kt c =
      SmoothForm.mpullback Prod.snd contMDiff_snd ω +
        mextDerivₗ _ 1 (floerGraphPrimitive Ks Kt c) :=
  (rfl)

/-- The exterior derivative `dλ_c = dK + c ds ∧ dt` of the one-form `λ_c`, evaluated on a pair of
tangent vectors `ζ = ((a, b), v)` and `ζ' = ((a', b'), v')`: it is
`dK_s(ζ) a' + dK_t(ζ) b' - (dK_s(ζ') a + dK_t(ζ') b) + c (a b' - b a')`. -/
theorem mextDerivₗ_floerGraphPrimitive_apply
    (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (c : ℝ) (p : (ℝ × ℝ) × M)
    (ζ ζ' : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    (mextDerivₗ _ 1 (floerGraphPrimitive Ks Kt c)).val p ![ζ, ζ'] =
      mvfderiv _ Ks p ζ * ζ'.1.1 + mvfderiv _ Kt p ζ * ζ'.1.2 -
          (mvfderiv _ Ks p ζ' * ζ.1.1 + mvfderiv _ Kt p ζ' * ζ.1.2) +
        c * (ζ.1.1 * ζ'.1.2 - ζ.1.2 * ζ'.1.1) := by
  -- `simp` matches the Leibniz lemma in `λ_c` only once its manifold is fixed to `(ℝ × ℝ) × M`.
  simp only [floerGraphPrimitive, map_add, map_smul, Submodule.coe_add, Submodule.coe_smul,
    Pi.add_apply, Pi.smul_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    mextDerivₗ_funSMulₗ_mextDerivₗ_ofFunction_apply (I := 𝓘(ℝ, ℝ × ℝ).prod I) (M := (ℝ × ℝ) × M),
    mvfderiv_coordS, mvfderiv_coordT]
  ring

/-- **The smooth taming form is Gromov's taming form.** At every point `p` of `(ℝ × ℝ) × M`, the
smooth two-form `Ω_c` evaluates on a pair of tangent vectors as the pointwise form
`TauCeti.SmoothTwoForm.floerGraphForm` of the curried perturbation components. -/
theorem eval₂_floerGraphTwoForm (ω : SmoothTwoForm I M)
    (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (c : ℝ) (p : (ℝ × ℝ) × M)
    (ζ ζ' : TangentSpace (𝓘(ℝ, ℝ × ℝ).prod I) p) :
    SmoothBundleForm.eval₂ (ω.floerGraphTwoForm Ks Kt c) p ζ ζ' =
      ω.floerGraphForm (fun z x ↦ Ks (z, x)) (fun z x ↦ Kt (z, x)) c p ζ ζ' := by
  rw [floerGraphTwoForm_def, SmoothBundleForm.eval₂_add, eval₂_mpullback_snd,
    SmoothBundleForm.eval₂_apply (mextDerivₗ _ 1 _), mextDerivₗ_floerGraphPrimitive_apply]
  refine Eq.trans ?_ (floerGraphForm_def ω _ _ c p ζ ζ').symm
  simp only [mvfderiv_eq_fderiv_add_mvfderiv, Manifold.tangentSpaceProdEquiv_apply]
  ring

/-- **Gromov's taming form is closed exactly when `ω` is.** It differs from the pullback of `ω`
to `(ℝ × ℝ) × M` by the exact form `dλ_c`, and pullback along the projection to `M`, a surjective
submersion, detects closedness. -/
theorem isClosed_floerGraphTwoForm_iff {ω : SmoothTwoForm I M}
    {Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯} {c : ℝ} :
    (ω.floerGraphTwoForm Ks Kt c).IsClosed ↔ ω.IsClosed := by
  rw [← isClosed_mpullback_iff_of_surjective (contMDiff_snd (I := 𝓘(ℝ, ℝ × ℝ)) (J := I))
    (fun x ↦ ⟨((0 : ℝ × ℝ), x), rfl⟩) fun p v ↦ ⟨((0 : ℝ × ℝ), v), by
      -- `ContinuousLinearMap.snd` reads the second component of a product tangent vector.
      rw [mfderiv_snd]; rfl⟩]
  refine ⟨fun h ↦ ?_, fun h ↦ h.add (isClosed_mextDerivₗ _)⟩
  have h' := h.sub (isClosed_mextDerivₗ (floerGraphPrimitive Ks Kt c))
  rwa [floerGraphTwoForm_def, add_sub_cancel_right] at h'

/-- **The energy of a graph, through the smooth taming form.** For a smooth map `u : ℝ × ℝ → M`,
the pullback of `Ω_c` along the graph `w ↦ (w, u w)` evaluates on the coordinate vectors `∂_s`,
`∂_t` to the Floer energy density of `u` plus `c + R_K(z, u z)`. -/
theorem IsNondegenerate.eval₂_mpullback_graph_floerGraphTwoForm [FiniteDimensional ℝ E]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    (Ks Kt : C^(⊤ : ℕ∞)⟮𝓘(ℝ, ℝ × ℝ).prod I, (ℝ × ℝ) × M; ℝ⟯) (c : ℝ) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) u) (z : ℝ × ℝ) :
    SmoothBundleForm.eval₂
        (SmoothForm.mpullback (fun w ↦ (w, u w)) (contMDiff_id.prodMk hu)
          (ω.floerGraphTwoForm Ks Kt c)) z stdComplexLineReal stdComplexLineImag =
      ω.floerEnergyDensity (fun z x ↦ Ks (z, x)) (fun z x ↦ Kt (z, x)) u z +
        (c + ω.hamiltonianCurvature (fun z x ↦ Ks (z, x)) (fun z x ↦ Kt (z, x)) z (u z)) := by
  have hu' : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z := (hu z).mdifferentiableAt (by simp)
  refine ((eval₂_mpullback _ _ _ _ _ _).trans (eval₂_floerGraphTwoForm _ _ _ _ _ _ _)).trans ?_
  -- The derivative of the graph sends a domain vector `v` to `(v, du v)`.
  have h := hω.floerGraphForm_graph (Ks := fun z x ↦ Ks (z, x)) (Kt := fun z x ↦ Kt (z, x)) u z c
  exact (congrArg₂ (ω.floerGraphForm _ _ c (z, u z)) (hu'.mfderiv_prodMk_id_apply _)
    (hu'.mfderiv_prodMk_id_apply _)).trans h

end TauCeti.SmoothTwoForm
