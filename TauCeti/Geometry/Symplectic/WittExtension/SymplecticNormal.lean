/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.WittExtension
public import TauCeti.LinearAlgebra.SesquilinearForm.SymplecticNormal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Extending a prescribed tangent and symplectic normal map

Let `B : V → V → Q` and `B' : V' → V' → Q'` be nondegenerate alternating bilinear maps on
finite-dimensional real vector spaces, with values in lines `Q` and `Q'`, and let `c : Q ≃ Q'` be
an identification of the lines. Let `W ≤ V` and `W' ≤ V'` be subspaces, and write
`W^⊥ ⧸ (W ∩ W^⊥)` for the symplectic normal space of `W` (`LinearMap.SymplecticNormal`), with its
induced line-valued form (`LinearMap.IsRefl.symplecticNormalForm`). Given

* a linear isomorphism `L : W ≃ W'` with `B'(L x, L y) = c (B(x, y))`, and
* a linear isomorphism `S` of symplectic normal spaces with the same property,

this file constructs a linear isomorphism `A : V ≃ V'` with `B'(A x, A y) = c (B(x, y))` which
restricts to `L` on `W` and induces `S` on symplectic normal spaces
(`LinearMap.IsAlt.exists_linearEquiv_extend_symplecticNormal`): `A` maps `W^⊥` into `W'^⊥`, and
the class of `A u` is `S [u]`. No dimension hypothesis is needed, since
`dim V = dim (W^⊥ ⧸ (W ∩ W^⊥)) + dim (W ∩ W^⊥) + dim W`
(`LinearMap.finrank_symplecticNormal_add_finrank_inf_add_finrank`) and `L` matches the radicals
`W ∩ W^⊥` and `W' ∩ W'^⊥`.

This is Witt's extension theorem with the normal data prescribed. Witt's theorem alone
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend_of_injective`) extends `L` to some
isometry, but the map it induces on the symplectic normal spaces is not controlled. Here `L` is
first combined with a lift of `S` to an isometric embedding of `W + W^⊥ ≅ W × (W^⊥ ⧸ (W ∩ W^⊥))`,
which Witt's theorem then extends.

For a contact structure `ξ` on a manifold `M`, the Levi form `ξ × ξ → TM ⧸ ξ` is of this kind,
with values in the contact line `TM ⧸ ξ`, and the symplectic normal space of the tangent image of
an isotropic map is its conformal symplectic normal space
(`TauCeti.ConformalSymplecticNormal`). The second theorem
(`LinearMap.IsAlt.exists_linearEquiv_extend_symplecticNormal_of_hyperplane`) treats this shape:
`B` is defined on a hyperplane `H ≤ V` with values in the line `V ⧸ H`. Given an identification
`c : V ⧸ H ≃ V' ⧸ H'` of the lines together with `L` and `S` as above, some `A : V ≃ V'` maps `H`
onto `H'`, induces `c` on the quotient lines and restricts on `H` to a map with all the properties
above. At a point of an isotropic submanifold, this is the linear tangent identification which
realizes a prescribed identification of contact lines and of conformal symplectic normal spaces,
the first-order input of the isotropic neighbourhood theorem of contact geometry.

## Main results

* `LinearMap.IsAlt.exists_linearEquiv_extend_of_injective`: Witt's extension theorem for
  line-valued forms, with the lines identified by `c`.
* `LinearMap.IsAlt.exists_linearEquiv_extend_symplecticNormal`: Witt's extension theorem with a
  prescribed map of symplectic normal spaces, for line-valued forms.
* `LinearMap.IsAlt.exists_linearEquiv_extend_symplecticNormal_of_hyperplane`: the same for a form
  on a hyperplane with values in the quotient line, extended to the whole space.

## References

* A. Weinstein, *Neighborhood classification of isotropic embeddings*, Journal of Differential
  Geometry 16 (1981), 125–128.
* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (the isotropic neighbourhood theorem and its linear algebra).
* E. Artin, *Geometric Algebra*, Interscience, 1957, Chapter III, Theorem 3.9 (Witt's theorem).
-/

public section

open Module Function

namespace LinearMap

variable {V V' Q Q' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  [AddCommGroup Q] [Module ℝ Q] [AddCommGroup Q'] [Module ℝ Q']
  {B : V →ₗ[ℝ] V →ₗ[ℝ] Q} {B' : V' →ₗ[ℝ] V' →ₗ[ℝ] Q'} {W : Submodule ℝ V} {W' : Submodule ℝ V'}

/-- If `σ` lifts classes of the symplectic normal space to `W^⊥`, then `(w, s) ↦ w + σ s` is
injective on `W × (W^⊥ ⧸ (W ∩ W^⊥))`. -/
private theorem injective_coprod_subtype {σ : SymplecticNormal B W →ₗ[ℝ] W.orthogonalBilin B}
    (hσ : ∀ s, Submodule.Quotient.mk (σ s) = s) :
    Injective (W.subtype.coprod ((W.orthogonalBilin B).subtype ∘ₗ σ)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨w, s⟩ h
  replace h : (w : V) + σ s = 0 := by simpa using h
  -- `σ s = -w` lies in `W`, so its class `s` vanishes, and then so does `w`.
  have hs : s = 0 := by
    rw [← hσ s, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      eq_neg_of_add_eq_zero_right h]
    exact W.neg_mem w.property
  subst hs
  simpa [Prod.ext_iff] using h

/-- An injective identification `e` of the values with `ℝ` turns a nondegenerate alternating
line-valued form into a symplectic form. -/
private def symplecticFormOfInjective [FiniteDimensional ℝ V] (hB : B.IsAlt)
    (hinj : Injective B) {e : Q →ₗ[ℝ] ℝ} (he : Injective e) : TauCeti.SymplecticForm V where
  toBilinForm := B.compr₂ e
  isAlt x := by simp [hB.self_eq_zero x]
  nondegenerate := .ofSeparatingLeft fun v hv ↦ hinj <| by
    ext w
    exact he (by simpa using hv w)

/-- **Witt's extension theorem for line-valued forms.** Let `B` and `B'` be nondegenerate
alternating forms on real vector spaces of the same finite dimension, with values in the lines `Q`
and `Q'`, and let `c : Q ≃ Q'`. If injective linear maps `g : X → V` and `f : X → V'` satisfy
`B'(f x, f y) = c (B(g x, g y))`, then some linear isomorphism `A : V ≃ V'` with
`B'(A x, A y) = c (B(x, y))` satisfies `A ∘ g = f`. -/
theorem IsAlt.exists_linearEquiv_extend_of_injective [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ V'] (hB : B.IsAlt) (hB' : B'.IsAlt) (hinj : Injective B)
    (hinj' : Injective B') (hQ : finrank ℝ Q = 1) (c : Q ≃ₗ[ℝ] Q')
    (hdim : finrank ℝ V = finrank ℝ V') {X : Type*} [AddCommGroup X] [Module ℝ X]
    {g : X →ₗ[ℝ] V} {f : X →ₗ[ℝ] V'} (hg : Injective g) (hf : Injective f)
    (hfg : ∀ x y, B' (f x) (f y) = c (B (g x) (g y))) :
    ∃ A : V ≃ₗ[ℝ] V', (∀ x y, B' (A x) (A y) = c (B x y)) ∧ ∀ x, A (g x) = f x := by
  -- Identify the lines with `ℝ` by `e` and `e ∘ c⁻¹`, and apply Witt's theorem to the resulting
  -- symplectic forms.
  have : FiniteDimensional ℝ Q := Module.finite_of_finrank_eq_succ hQ
  let e : Q ≃ₗ[ℝ] ℝ := LinearEquiv.ofFinrankEq Q ℝ (by rw [hQ, Module.finrank_self])
  let ω := symplecticFormOfInjective hB hinj e.injective
  let ω' := symplecticFormOfInjective hB' hinj' (c.symm.trans e).injective
  -- The values of `ω` and `ω'`, by the definition of `symplecticFormOfInjective`.
  have hω (x y : V) : ω x y = e (B x y) := (rfl)
  have hω' (x y : V') : ω' x y = e (c.symm (B' x y)) := (rfl)
  obtain ⟨A, hA, hAext⟩ := TauCeti.SymplecticForm.exists_isSymplectomorphism_extend_of_injective
    ω ω' hdim hg hf fun x y ↦ by rw [hω', hω, hfg, c.symm_apply_apply]
  refine ⟨A, fun x y ↦ ?_, hAext⟩
  have h := hA.apply x y
  rwa [hω', hω, e.injective.eq_iff, c.symm_apply_eq] at h

/-- **Witt's extension theorem with a prescribed symplectic normal map.** Let `B` and `B'` be
nondegenerate alternating forms on finite-dimensional real vector spaces, with values in the lines
`Q` and `Q'`, and let `c : Q ≃ Q'`. Let `L : W ≃ W'` be a linear isomorphism of subspaces and `S`
one of their symplectic normal spaces `W^⊥ ⧸ (W ∩ W^⊥) ≃ W'^⊥ ⧸ (W' ∩ W'^⊥)`, both carrying the
forms to the forms up to `c`: `B'(L x, L y) = c (B(x, y))`, and likewise for `S` and the induced
forms. Then some linear isomorphism `A : V ≃ V'` satisfies `B'(A x, A y) = c (B(x, y))`, restricts
to `L` on `W`, and induces `S`: it maps each `u ∈ W^⊥` to a vector `u' ∈ W'^⊥` whose class is
`S [u]`. -/
theorem IsAlt.exists_linearEquiv_extend_symplecticNormal [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ V'] (hB : B.IsAlt) (hB' : B'.IsAlt) (hinj : Injective B)
    (hinj' : Injective B') (hQ : finrank ℝ Q = 1) (c : Q ≃ₗ[ℝ] Q') (L : W ≃ₗ[ℝ] W')
    (hL : ∀ x y : W, B' (L x) (L y) = c (B x y))
    (S : SymplecticNormal B W ≃ₗ[ℝ] SymplecticNormal B' W')
    (hS : ∀ u v, hB'.isRefl.symplecticNormalForm W' (S u) (S v) =
      c (hB.isRefl.symplecticNormalForm W u v)) :
    ∃ A : V ≃ₗ[ℝ] V', (∀ x y, B' (A x) (A y) = c (B x y)) ∧ (∀ w : W, A w = L w) ∧
      ∀ u : W.orthogonalBilin B, ∃ u' : W'.orthogonalBilin B', (u' : V') = A u ∧
        S (Submodule.Quotient.mk u) = Submodule.Quotient.mk u' := by
  -- Lifts `σ`, `σ'` of the symplectic normal spaces to `W^⊥` and `W'^⊥`.
  obtain ⟨σ, hσ⟩ := (W.comap (W.orthogonalBilin B).subtype).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _)
  obtain ⟨σ', hσ'⟩ :=
    (W'.comap (W'.orthogonalBilin B').subtype).mkQ.exists_rightInverse_of_surjective
      (Submodule.range_mkQ _)
  have hσ_mk (s) : Submodule.Quotient.mk (σ s) = s := LinearMap.congr_fun hσ s
  have hσ'_mk (s) : Submodule.Quotient.mk (σ' s) = s := LinearMap.congr_fun hσ' s
  -- The embeddings `g : (w, s) ↦ w + σ s` and `f : (w, s) ↦ L w + σ' (S s)` of
  -- `W × (W^⊥ ⧸ (W ∩ W^⊥))` into `V` and `V'`.
  let g : W × SymplecticNormal B W →ₗ[ℝ] V :=
    W.subtype.coprod ((W.orthogonalBilin B).subtype ∘ₗ σ)
  let f : W × SymplecticNormal B W →ₗ[ℝ] V' :=
    W'.subtype.coprod ((W'.orthogonalBilin B').subtype ∘ₗ σ') ∘ₗ (L.prodCongr S).toLinearMap
  have hg (w : W) (s) : g (w, s) = w + σ s := by simp [g]
  have hf (w : W) (s) : f (w, s) = L w + σ' (S s) := by simp [f]
  have hginj : Injective g := injective_coprod_subtype hσ_mk
  have hfinj : Injective f := (injective_coprod_subtype hσ'_mk).comp (L.prodCongr S).injective
  -- `B'(f x, f y) = c (B(g x, g y))`.
  have hfg (x y) : B' (f x) (f y) = c (B (g x) (g y)) := by
    obtain ⟨w₁, s₁⟩ := x
    obtain ⟨w₂, s₂⟩ := y
    rw [hf, hf, hg, hg, hB'.isRefl.apply_add_add_of_mem (L w₁).property (L w₂).property (σ'
        (S s₁)).property
      (σ' (S s₂)).property, hB.isRefl.apply_add_add_of_mem w₁.property w₂.property (σ s₁).property
          (σ s₂).property, map_add, hL,
      ← hB'.isRefl.symplecticNormalForm_mk (W := W'), hσ'_mk, hσ'_mk, hS,
      ← hB.isRefl.symplecticNormalForm_mk (W := W), hσ_mk, hσ_mk]
  have hdim : finrank ℝ V = finrank ℝ V' := by
    rw [← finrank_symplecticNormal_add_finrank_inf_add_finrank W hinj hQ,
      ← finrank_symplecticNormal_add_finrank_inf_add_finrank W' hinj' (c.finrank_eq ▸ hQ),
      S.finrank_eq, L.finrank_eq,
      Submodule.finrank_inf_orthogonalBilin_eq_of_isometry c.injective L hL]
  obtain ⟨A, hAB, hAext⟩ :=
    hB.exists_linearEquiv_extend_of_injective hB' hinj hinj' hQ c hdim hginj hfinj hfg
  have hAL (w : W) : A w = L w := by simpa [hg, hf] using hAext (w, 0)
  refine ⟨A, hAB, hAL, fun u ↦ ⟨⟨A u, fun n hn ↦ ?_⟩, rfl, ?_⟩⟩
  · -- `A` maps `W^⊥` into `W'^⊥`, as it maps `W` onto `W'` isometrically up to `c`.
    obtain ⟨m, hm⟩ := L.surjective ⟨n, hn⟩
    rw [show n = L m by rw [hm], ← hAL, hAB, u.property m m.property, map_zero]
  · -- `u` differs from `σ [u]` by a vector `w` of `W`, so `A u` differs from `σ' (S [u])` by
    -- `L w ∈ W'`.
    have hu : ((σ (Submodule.Quotient.mk u) : V) - u) ∈ W := by
      simpa [Submodule.Quotient.eq] using hσ_mk (Submodule.Quotient.mk u)
    have hAσ : A (σ (Submodule.Quotient.mk u)) = σ' (S (Submodule.Quotient.mk u)) := by
      simpa [hg, hf] using hAext (0, Submodule.Quotient.mk u)
    have hAu : A u = σ' (S (Submodule.Quotient.mk u)) - L ⟨_, hu⟩ := by
      rw [← hAL, ← hAσ, ← map_sub, sub_sub_cancel]
    rw [← hσ'_mk (S (Submodule.Quotient.mk u)), Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_sub]
    simp [hAu]

/-- **Witt's extension theorem with prescribed normal data, for a form on a hyperplane.** Let
`H ≤ V` and `H' ≤ V'` be hyperplanes of finite-dimensional real vector spaces, carrying
nondegenerate alternating forms `B` and `B'` with values in the lines `V ⧸ H` and `V' ⧸ H'`, as the
Levi form of a contact structure takes values in its contact line. Let `c : V ⧸ H ≃ V' ⧸ H'`, and
let `L : W ≃ W'` and `S : W^⊥ ⧸ (W ∩ W^⊥) ≃ W'^⊥ ⧸ (W' ∩ W'^⊥)`, for subspaces `W ≤ H` and
`W' ≤ H'`, carry the forms to the forms up to `c`, as in
`LinearMap.IsAlt.exists_linearEquiv_extend_symplecticNormal`. Then some linear isomorphism
`A : V ≃ V'` maps `H` onto `H'` by a linear isomorphism `A₀ : H ≃ H'` and induces `c` on the
quotient lines, and `A₀` satisfies `B'(A₀ x, A₀ y) = c (B(x, y))`, restricts to `L` on `W` and
induces `S`. -/
theorem IsAlt.exists_linearEquiv_extend_symplecticNormal_of_hyperplane [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ V'] {H : Submodule ℝ V} {H' : Submodule ℝ V'}
    {B : H →ₗ[ℝ] H →ₗ[ℝ] V ⧸ H} {B' : H' →ₗ[ℝ] H' →ₗ[ℝ] V' ⧸ H'} (hB : B.IsAlt) (hB' : B'.IsAlt)
    (hinj : Injective B) (hinj' : Injective B') (hH : finrank ℝ (V ⧸ H) = 1)
    (c : (V ⧸ H) ≃ₗ[ℝ] V' ⧸ H') {W : Submodule ℝ H} {W' : Submodule ℝ H'} (L : W ≃ₗ[ℝ] W')
    (hL : ∀ x y : W, B' (L x) (L y) = c (B x y))
    (S : SymplecticNormal B W ≃ₗ[ℝ] SymplecticNormal B' W')
    (hS : ∀ u v, hB'.isRefl.symplecticNormalForm W' (S u) (S v) =
      c (hB.isRefl.symplecticNormalForm W u v)) :
    ∃ A : V ≃ₗ[ℝ] V', ∃ A₀ : H ≃ₗ[ℝ] H', (∀ x : H, A x = A₀ x) ∧
      (∀ v, H'.mkQ (A v) = c (H.mkQ v)) ∧ (∀ x y, B' (A₀ x) (A₀ y) = c (B x y)) ∧
      (∀ w : W, A₀ w = L w) ∧
      ∀ u : W.orthogonalBilin B, ∃ u' : W'.orthogonalBilin B', (u' : H') = A₀ u ∧
        S (Submodule.Quotient.mk u) = Submodule.Quotient.mk u' := by
  obtain ⟨A₀, hA₀B, hA₀L, hA₀S⟩ :=
    hB.exists_linearEquiv_extend_symplecticNormal hB' hinj hinj' hH c L hL S hS
  -- Extend `A₀` across complements `C` of `H` and `C'` of `H'`, identified with the quotient
  -- lines, by `c`.
  obtain ⟨C, hC⟩ := H.exists_isCompl
  obtain ⟨C', hC'⟩ := H'.exists_isCompl
  let φ : C ≃ₗ[ℝ] C' := (H.quotientEquivOfIsCompl C hC).symm.trans
    (c.trans (H'.quotientEquivOfIsCompl C' hC'))
  let A : V ≃ₗ[ℝ] V' := (H.prodEquivOfIsCompl C hC).symm.trans
    ((A₀.prodCongr φ).trans (H'.prodEquivOfIsCompl C' hC'))
  have hA (x : H) (y : C) : A (x + y) = A₀ x + φ y := by
    simp only [← Submodule.coe_prodEquivOfIsCompl' H C hC (x, y), A, LinearEquiv.trans_apply]
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl']
  refine ⟨A, A₀, fun x ↦ by simpa using hA x 0, fun v ↦ ?_, hA₀B, hA₀L, hA₀S⟩
  obtain ⟨⟨x, y⟩, rfl⟩ := (H.prodEquivOfIsCompl C hC).surjective v
  rw [Submodule.coe_prodEquivOfIsCompl', hA]
  simp [φ, Submodule.mk_quotientEquivOfIsCompl_apply, (Submodule.Quotient.mk_eq_zero H).2
      x.property,
    (Submodule.Quotient.mk_eq_zero H').2 (A₀ x).property]

end LinearMap
