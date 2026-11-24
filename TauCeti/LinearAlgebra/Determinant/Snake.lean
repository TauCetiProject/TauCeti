/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.SnakeLemma
public import TauCeti.LinearAlgebra.Determinant.DirectSum

/-!
# The determinant line of a map of short exact sequences

Consider a commutative diagram of vector spaces whose rows are short exact,
```
0 → M₁ -f₁→ M₂ -f₂→ M₃ → 0
    |       |       |
    i₁      i₂      i₃
    ↓       ↓       ↓
0 → N₁ -g₁→ N₂ -g₂→ N₃ → 0
```
and in which the outer vertical maps have finite-dimensional kernels and cokernels. The snake
lemma gives the six-term exact sequence

`0 → ker i₁ → ker i₂ → ker i₃ → coker i₁ → coker i₂ → coker i₃ → 0`

of `TauCeti.Algebra.Module.SnakeLemma`, whose alternating sum of dimensions is the additivity of
the index, `index i₂ = index i₁ + index i₃` (`LinearMap.index_eq_add_of_exact`). Its determinant
lines give the finer, canonical statement

`det i₂ ≃ det i₁ ⊗ det i₃`

for the determinant lines `det i = det (ker i) ⊗ (det (coker i))^*` (`LinearMap.detLine`), with no
choice of bases, complements or splittings of the rows (`LinearMap.detLineEquivOfExact`). This is
`TauCeti.detLineSixTermEquiv` for the snake sequence. Its value on exterior products is
`LinearMap.detLineEquivOfExact_tmul`.

For Fredholm operators this is the isomorphism of determinant lines attached to an exact triple of
operators `0 → i₁ → i₂ → i₃ → 0`: orientations of the determinant lines of `i₁` and `i₃` orient
that of `i₂`.

For a direct sum `f.prodMap g`, with the split rows `0 → M → M × M' → M' → 0` and
`0 → N → N × N' → N' → 0`, the connecting map vanishes and the isomorphism is the direct-sum
isomorphism `LinearMap.detLineProdMapEquiv` up to the sign `(-1) ^ (dim (coker f) * dim (ker g))`
(`LinearMap.detLineEquivOfExact_prodMap`). The sign is the Koszul sign that
`LinearMap.detLineProdMapEquiv` pays to move `(det (coker f))^*` past `det (ker g)`; the snake
sequence never moves them.

## Main declarations

* `LinearMap.detLineEquivOfExact`: the isomorphism `det i₂ ≃ det i₁ ⊗ det i₃`.
* `LinearMap.detLineEquivOfExact_tmul`: its value on exterior products.
* `LinearMap.detLineEquivOfExact_prodMap`: its comparison with `LinearMap.detLineProdMapEquiv` for
  direct sums.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368 (the isomorphisms
  attached to exact triples of Fredholm operators).
-/

public section

noncomputable section

open Function Module TensorProduct

namespace LinearMap

variable {K : Type*} [Field K]

section Snake

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
  [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂] [AddCommGroup M₃] [Module K M₃]
  [AddCommGroup N₁] [Module K N₁] [AddCommGroup N₂] [Module K N₂] [AddCommGroup N₃] [Module K N₃]
  {f₁ : M₁ →ₗ[K] M₂} {f₂ : M₂ →ₗ[K] M₃} {g₁ : N₁ →ₗ[K] N₂} {g₂ : N₂ →ₗ[K] N₃}
  {i₁ : M₁ →ₗ[K] N₁} {i₂ : M₂ →ₗ[K] N₂} {i₃ : M₃ →ₗ[K] N₃}
  [FiniteDimensional K (ker i₁)] [FiniteDimensional K (ker i₃)]
  [FiniteDimensional K (N₁ ⧸ range i₁)] [FiniteDimensional K (N₃ ⧸ range i₃)]

/-- **The determinant line of a map of short exact sequences.** For a commutative diagram
`g₁ ∘ i₁ = i₂ ∘ f₁`, `g₂ ∘ i₂ = i₃ ∘ f₂` whose rows `0 → M₁ → M₂ → M₃ → 0` and
`0 → N₁ → N₂ → N₃ → 0` are short exact, and whose outer vertical maps have finite-dimensional
kernels and cokernels, the canonical isomorphism `det i₂ ≃ det i₁ ⊗ det i₃` of determinant lines.
It is `TauCeti.detLineSixTermEquiv` for the snake sequence
`0 → ker i₁ → ker i₂ → ker i₃ → coker i₁ → coker i₂ → coker i₃ → 0`; its value on exterior
products is `LinearMap.detLineEquivOfExact_tmul`. -/
def detLineEquivOfExact (hf : Exact f₁ f₂) (hg : Exact g₁ g₂) (hf₁ : Injective f₁)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) :
    i₂.detLine ≃ₗ[K] i₁.detLine ⊗[K] i₃.detLine :=
  have := finiteDimensional_coker₂_of_finiteDimensional_coker₁₃ hg hf₂ h₁ h₂
  TauCeti.detLineSixTermEquiv (injective_restrict hf₁ fun _ ↦ map_mem_ker_of_comp_eq f₁ h₁)
    (hf.restrict_ker hg₁ h₁ h₂) (hf.restrict_ker_snakeδ hg hf₂ hg₁ h₁ h₂)
    (hf.snakeδ_mapQ_range hg hf₂ hg₁ h₁ h₂) (hg.mapQ_range hf₂ h₁ h₂)
    (Submodule.mapQ_surjective _ _ g₂ (range_le_comap_range_of_comp_eq h₂) hg₂)

/-- **The value of `LinearMap.detLineEquivOfExact` on exterior products.** Choose `u`, a family of
`dim (ker i₁)` vectors of `ker i₁`, and families `v`, `w`, `x` and `y` in `ker i₂`, `ker i₃`,
`coker i₁` and `coker i₂` whose images complete them along the snake sequence
`0 → ker i₁ → ker i₂ → ker i₃ → coker i₁ → coker i₂ → coker i₃ → 0`. Let `β`, `γ`, `δ` and `ε` be
the exterior products in `ker i₂`, `ker i₃`, `coker i₁` and `coker i₂` of the images of `u`, `v`,
`w` and `x` followed by `v`, `w`, `x` and `y`. If `ψ` takes the value `1` at `δ` and `χ` takes the
value `1` at the exterior product of the classes of `y` in `coker i₃`, then `β ⊗ φ` goes to
`φ ε • ((α ⊗ ψ) ⊗ (γ ⊗ χ))`, with `α` the exterior product of `u`. -/
theorem detLineEquivOfExact_tmul (hf : Exact f₁ f₂) (hg : Exact g₁ g₂) (hf₁ : Injective f₁)
    (hf₂ : Surjective f₂) (hg₁ : Injective g₁) (hg₂ : Surjective g₂)
    (h₁ : g₁ ∘ₗ i₁ = i₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ i₂ = i₃ ∘ₗ f₂) (u : Fin (finrank K (ker i₁)) → ker i₁)
    (v : Fin (finrank K (range (f₂.restrict fun _ ↦ map_mem_ker_of_comp_eq f₂ h₂))) → ker i₂)
    (w : Fin (finrank K (range (hf.snakeδ hg hf₂ hg₁ h₁ h₂))) → ker i₃)
    (x : Fin (finrank K (range ((range i₁).mapQ (range i₂) g₁
      (range_le_comap_range_of_comp_eq h₁)))) → N₁ ⧸ range i₁)
    (y : Fin (finrank K (N₃ ⧸ range i₃)) → N₂ ⧸ range i₂)
    {β : TauCeti.detLine K (ker i₂)} (hβ : (β : ExteriorAlgebra K (ker i₂)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append ((f₁.restrict fun _ ↦ map_mem_ker_of_comp_eq f₁ h₁) ∘ u) v))
    {γ : TauCeti.detLine K (ker i₃)} (hγ : (γ : ExteriorAlgebra K (ker i₃)) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append ((f₂.restrict fun _ ↦ map_mem_ker_of_comp_eq f₂ h₂) ∘ v) w))
    {δ : TauCeti.detLine K (N₁ ⧸ range i₁)} (hδ : (δ : ExteriorAlgebra K (N₁ ⧸ range i₁)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (hf.snakeδ hg hf₂ hg₁ h₁ h₂ ∘ w) x))
    {ε : TauCeti.detLine K (N₂ ⧸ range i₂)} (hε : (ε : ExteriorAlgebra K (N₂ ⧸ range i₂)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append
        ((range i₁).mapQ (range i₂) g₁ (range_le_comap_range_of_comp_eq h₁) ∘ x) y))
    (φ : Dual K (TauCeti.detLine K (N₂ ⧸ range i₂)))
    {ψ : Dual K (TauCeti.detLine K (N₁ ⧸ range i₁))} (hψ : ψ δ = 1)
    {χ : Dual K (TauCeti.detLine K (N₃ ⧸ range i₃))}
    (hχ : χ (exteriorPower.ιMulti K _
      ((range i₂).mapQ (range i₃) g₂ (range_le_comap_range_of_comp_eq h₂) ∘ y)) = 1) :
    detLineEquivOfExact hf hg hf₁ hf₂ hg₁ hg₂ h₁ h₂ (β ⊗ₜ φ) =
      φ ε • ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ (γ ⊗ₜ χ)) :=
  have := finiteDimensional_coker₂_of_finiteDimensional_coker₁₃ hg hf₂ h₁ h₂
  TauCeti.detLineSixTermEquiv_tmul _ _ _ _ _ _ u v w x y hβ hγ hδ hε φ hψ hχ

end Snake

section Prod

/-! ### Split sequences -/

variable {M N M' N' : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N'] (f : M →ₗ[K] N)
  (g : M' →ₗ[K] N') [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]

/-- **The value of `LinearMap.detLineEquivOfExact` on a direct sum.** For the split rows
`0 → M → M × M' → M' → 0` and `0 → N → N × N' → N' → 0` and `i₂ = f.prodMap g`, the connecting map
vanishes. Let `β` be the exterior product of kernel vectors `(uᵢ, 0)` followed by `(0, wⱼ)`, and
`ε` that of the classes of `(yfᵢ, 0)` followed by `(0, ygⱼ)` in the cokernel of `f.prodMap g`. If
`ψ` and `χ` take the value `1` at the exterior products of the classes of `yf` in `coker f` and of
`yg` in `coker g`, then `β ⊗ φ` goes to `φ ε • ((α ⊗ ψ) ⊗ (γ ⊗ χ))`, where `α` and `γ` are the
exterior products of `u` and `w`. -/
private theorem detLineEquivOfExact_prodMap_tmul (u : Fin (finrank K (ker f)) → ker f)
    (w : Fin (finrank K (ker g)) → ker g) {β : TauCeti.detLine K (ker (f.prodMap g))}
    (hβ : (β : ExteriorAlgebra K (ker (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (fun i ↦ ⟨(u i, 0), by simp⟩) fun j ↦ ⟨(0, w j), by simp⟩))
    (yf : Fin (finrank K (N ⧸ range f)) → N) (yg : Fin (finrank K (N' ⧸ range g)) → N')
    {ε : TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g))}
    (hε : (ε : ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (fun i ↦ (range (f.prodMap g)).mkQ (yf i, 0))
        fun j ↦ (range (f.prodMap g)).mkQ (0, yg j)))
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g))))
    {ψ : Dual K (TauCeti.detLine K (N ⧸ range f))}
    (hψ : ψ (exteriorPower.ιMulti K _ ((range f).mkQ ∘ yf)) = 1)
    {χ : Dual K (TauCeti.detLine K (N' ⧸ range g))}
    (hχ : χ (exteriorPower.ιMulti K _ ((range g).mkQ ∘ yg)) = 1) :
    detLineEquivOfExact Exact.inl_snd Exact.inl_snd (inl_injective (R := K))
        (snd_surjective (R := K)) (inl_injective (R := K)) (snd_surjective (R := K))
        (prodMap_comp_inl f g).symm (snd_comp_prodMap f g) (β ⊗ₜ φ) =
      φ ε • ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ (exteriorPower.ιMulti K _ w ⊗ₜ χ)) := by
  have h₁ := (prodMap_comp_inl f g).symm
  have h₂ := snd_comp_prodMap f g
  have hf := Exact.inl_snd (R := K) (M := M) (N := M')
  have hg := Exact.inl_snd (R := K) (M := N) (N := N')
  -- The maps of the snake sequence `ker f → ker (f.prodMap g) → ker g → coker f → ⋯`.
  set F₂ := (snd K M M').restrict fun _ ↦ map_mem_ker_of_comp_eq (snd K M M') h₂
  set δ := hf.snakeδ hg snd_surjective inl_injective h₁ h₂
  set F₄ := (range f).mapQ (range (f.prodMap g)) (inl K N N') (range_le_comap_range_of_comp_eq h₁)
  set F₅ := (range (f.prodMap g)).mapQ (range g) (snd K N N')
    (range_le_comap_range_of_comp_eq h₂)
  -- The connecting map vanishes, so the snake sequence splits into kernels and cokernels.
  have hδ : δ = 0 := snakeδ_prodMap_eq_zero f g
  have hv : finrank K (range F₂) = finrank K (ker g) := by
    rw [range_eq_top.2 fun z ↦ ⟨⟨(0, z), by simp⟩, rfl⟩, finrank_top]
  have hw : finrank K (range δ) = 0 := by rw [hδ, range_zero, finrank_bot]
  have hx : finrank K (range F₄) = finrank K (N ⧸ range f) := finrank_range_of_inj <| by
    have h : Exact δ F₄ := hf.snakeδ_mapQ_range hg snd_surjective inl_injective h₁ h₂
    rwa [hδ, exact_zero_iff_injective] at h
  -- The data of `LinearMap.detLineEquivOfExact_tmul`: `(0, wⱼ)` lifts `w`, the connecting map
  -- contributes no vectors, and the classes of `(yfᵢ, 0)` and `(0, ygⱼ)` lift `yf` and `yg`.
  let F₁ := (inl K M M').restrict fun _ ↦ map_mem_ker_of_comp_eq (inl K M M') h₁
  let v : Fin (finrank K (range F₂)) → ker (f.prodMap g) :=
    (fun j ↦ ⟨(0, w j), by simp⟩) ∘ Fin.cast hv
  let x : Fin (finrank K (range F₄)) → N ⧸ range f := ((range f).mkQ ∘ yf) ∘ Fin.cast hx
  let y : Fin (finrank K (N' ⧸ range g)) → (N × N') ⧸ range (f.prodMap g) :=
    fun j ↦ (range (f.prodMap g)).mkQ (0, yg j)
  have hβ' : (β : ExteriorAlgebra K (ker (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (F₁ ∘ u) v) := by
    rw [show F₁ ∘ u = fun i ↦ ⟨(u i, 0), by simp⟩ from funext fun i ↦ by ext <;> simp [F₁],
      Fin.append_cast_right, TauCeti.ExteriorAlgebra.ιMulti_comp_cast, hβ]
  have hγ' : ((exteriorPower.ιMulti K _ w : TauCeti.detLine K (ker g)) :
      ExteriorAlgebra K (ker g)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (F₂ ∘ v) (fun _ : Fin (finrank K (range δ)) ↦ 0)) := by
    rw [exteriorPower.ιMulti_apply_coe, Fin.append_right_nil _ _ hw,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
    exact (TauCeti.ExteriorAlgebra.ιMulti_comp_cast hv w).symm
  have hδ' : ((exteriorPower.ιMulti K _ ((range f).mkQ ∘ yf) : TauCeti.detLine K (N ⧸ range f)) :
      ExteriorAlgebra K (N ⧸ range f)) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (δ ∘ fun _ : Fin (finrank K (range δ)) ↦ 0) x) := by
    rw [exteriorPower.ιMulti_apply_coe, Fin.append_left_nil _ _ hw,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  have hε' : (ε : ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (F₄ ∘ x) y) := by
    rw [show F₄ ∘ x = (fun i ↦ (range (f.prodMap g)).mkQ (yf i, 0)) ∘ Fin.cast hx from
      funext fun i ↦ by simp [x, F₄], Fin.append_cast_left,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast, hε]
  have hχ' : χ (exteriorPower.ιMulti K _ (F₅ ∘ y)) = 1 := by
    rwa [show F₅ ∘ y = (range g).mkQ ∘ yg from funext fun j ↦ by simp [F₅, y]]
  exact detLineEquivOfExact_tmul hf hg inl_injective snd_surjective inl_injective snd_surjective
    h₁ h₂ u v (fun _ ↦ 0) x y hβ' hγ' hδ' hε' φ hψ hχ'

/-- `LinearMap.detLineEquivOfExact_prodMap` on `β ⊗ φ`, for `β` the exterior product of kernel
vectors `(uᵢ, 0)` followed by `(0, wⱼ)` of `f.prodMap g`. -/
private theorem detLineEquivOfExact_prodMap_tmul_eq_smul (u : Fin (finrank K (ker f)) → ker f)
    (w : Fin (finrank K (ker g)) → ker g) {β : TauCeti.detLine K (ker (f.prodMap g))}
    (hβ : (β : ExteriorAlgebra K (ker (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
      (Fin.append (fun i ↦ ⟨(u i, 0), by simp⟩) fun j ↦ ⟨(0, w j), by simp⟩))
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)))) :
    detLineEquivOfExact Exact.inl_snd Exact.inl_snd (inl_injective (R := K))
        (snd_surjective (R := K)) (inl_injective (R := K)) (snd_surjective (R := K))
        (prodMap_comp_inl f g).symm (snd_comp_prodMap f g) (β ⊗ₜ φ) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        detLineProdMapEquiv f g (β ⊗ₜ φ) := by
  -- Lifts of bases of `coker f` and `coker g`, and functionals normalized on their products.
  have hcf := (exteriorPower.ιMulti_ne_zero_iff _).2
    (Module.finBasis K (N ⧸ range f)).linearIndependent
  have hcg := (exteriorPower.ιMulti_ne_zero_iff _).2
    (Module.finBasis K (N' ⧸ range g)).linearIndependent
  choose yf hyf using fun i ↦ (range f).mkQ_surjective (Module.finBasis K (N ⧸ range f) i)
  choose yg hyg using fun j ↦ (range g).mkQ_surjective (Module.finBasis K (N' ⧸ range g) j)
  rw [← show (range f).mkQ ∘ yf = _ from funext hyf] at hcf
  rw [← show (range g).mkQ ∘ yg = _ from funext hyg] at hcg
  choose ψ hψ using Module.Projective.exists_dual_eq_one K hcf
  choose χ hχ using Module.Projective.exists_dual_eq_one K hcg
  -- The exterior product of the classes of `(yfᵢ, 0)` and `(0, ygⱼ)`.
  have hc : finrank K ((N × N') ⧸ range (f.prodMap g)) =
      finrank K (N ⧸ range f) + finrank K (N' ⧸ range g) := by
    rw [((Submodule.quotEquivOfEq _ _ (range_prodMap f g)).trans
      (Submodule.quotientProdEquiv _ _)).finrank_eq, Module.finrank_prod]
  choose ε hε using (show ∃ ε : TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)),
      (ε : ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
        (Fin.append (fun i ↦ (range (f.prodMap g)).mkQ (yf i, 0))
          fun j ↦ (range (f.prodMap g)).mkQ (0, yg j)) from
    ⟨exteriorPower.ιMulti K _ (Fin.append _ _ ∘ Fin.cast hc), by
      rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]⟩)
  have hL := detLineEquivOfExact_prodMap_tmul f g u w hβ yf yg hε φ hψ hχ
  have hR := detLineProdMapEquiv_tmul f g u w yf yg hβ hε φ
  have hsign (a : K) (t : TauCeti.detLine K (ker f) ⊗[K] TauCeti.detLine K (ker g)) :
      a • t = (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        (((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) * a) • t) := by
    rw [smul_smul, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  -- Pairing with the classes of `yf` and `yg` is injective; both sides pair to `φ ε • (α ⊗ γ)`.
  let E := TensorProduct.map
    ((TensorProduct.rid K (TauCeti.detLine K (ker f))).toLinearMap ∘ₗ
      (Dual.eval K _ (exteriorPower.ιMulti K _ ((range f).mkQ ∘ yf))).lTensor _)
    ((TensorProduct.rid K (TauCeti.detLine K (ker g))).toLinearMap ∘ₗ
      (Dual.eval K _ (exteriorPower.ιMulti K _ ((range g).mkQ ∘ yg))).lTensor _)
  refine TensorProduct.map_injective_of_flat_flat _ _
    (TauCeti.rid_lTensor_eval_injective (TauCeti.finrank_detLine K _) hcf)
    (TauCeti.rid_lTensor_eval_injective (TauCeti.finrank_detLine K _) hcg) (?_ : E _ = E _)
  calc E _ = E (φ ε • ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ
        (exteriorPower.ιMulti K _ w ⊗ₜ χ))) := congrArg E hL
    _ = φ ε • (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w) := by
      simp only [E, LinearMap.map_smul, TensorProduct.map_tmul, LinearMap.comp_apply,
        LinearMap.lTensor_tmul, Dual.eval_apply, hψ, hχ, LinearEquiv.coe_coe,
        TensorProduct.rid_tmul, one_smul]
    _ = (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        (((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) * φ ε) •
          (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w)) := hsign _ _
    _ = (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        E (detLineProdMapEquiv f g (β ⊗ₜ φ)) := congrArg _ hR.symm
    _ = E _ := (LinearMap.map_smul E _ _).symm

omit [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)] in
/-- The exterior product of a basis of `ker f`, placed in `ker f × 0`, followed by a basis of
`ker g`, placed in `0 × ker g`, is a nonzero element of the line `det (ker (f.prodMap g))`. -/
private theorem exists_ιMulti_append_ne_zero :
    ∃ β : TauCeti.detLine K (ker (f.prodMap g)),
      (β : ExteriorAlgebra K (ker (f.prodMap g))) = ExteriorAlgebra.ιMulti K _
        (Fin.append (fun i ↦ ⟨(Module.finBasis K (ker f) i, 0), by simp⟩)
          fun j ↦ ⟨(0, Module.finBasis K (ker g) j), by simp⟩) ∧ β ≠ 0 := by
  have hv : LinearIndependent K (Fin.append
      (fun i ↦ (⟨(Module.finBasis K (ker f) i, 0), by simp⟩ : ker (f.prodMap g)))
      fun j ↦ ⟨(0, Module.finBasis K (ker g) j), by simp⟩) := by
    refine LinearIndependent.of_comp (ker (f.prodMap g)).subtype ?_
    convert (linearIndependent_inl_union_inr'
      ((Module.finBasis K (ker f)).linearIndependent.map' (ker f).subtype
        (Submodule.ker_subtype _))
      ((Module.finBasis K (ker g)).linearIndependent.map' (ker g).subtype
        (Submodule.ker_subtype _))).comp _ finSumFinEquiv.symm.injective using 1
    funext i
    refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp
  have hk : finrank K (ker (f.prodMap g)) = finrank K (ker f) + finrank K (ker g) := by
    rw [((LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)).finrank_eq,
      Module.finrank_prod]
  exact ⟨exteriorPower.ιMulti K _ (Fin.append _ _ ∘ Fin.cast hk), by
    rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_comp_cast],
    (exteriorPower.ιMulti_ne_zero_iff _).2 (hv.comp _ (Fin.cast_injective hk))⟩

/-- **The determinant line of a split sequence.** For the split rows `0 → M → M × M' → M' → 0` and
`0 → N → N × N' → N' → 0` and the vertical maps `f`, `f.prodMap g` and `g`, the isomorphism
`LinearMap.detLineEquivOfExact` is the direct-sum isomorphism `LinearMap.detLineProdMapEquiv` up to
the sign `(-1) ^ (dim (coker f) * dim (ker g))`. Here the connecting map vanishes, and the snake
sequence keeps `(det (coker f))^*` after `det (ker g)`, where `LinearMap.detLineProdMapEquiv` pays
the Koszul sign of moving it past. -/
theorem detLineEquivOfExact_prodMap :
    (detLineEquivOfExact Exact.inl_snd Exact.inl_snd (inl_injective (R := K))
        (snd_surjective (R := K)) (inl_injective (R := K)) (snd_surjective (R := K))
        (prodMap_comp_inl f g).symm (snd_comp_prodMap f g) :
        (f.prodMap g).detLine →ₗ[K] f.detLine ⊗[K] g.detLine) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) •
        (detLineProdMapEquiv f g : (f.prodMap g).detLine →ₗ[K] f.detLine ⊗[K] g.detLine) := by
  -- Both sides are linear, and agree on `β ⊗ φ` for the spanning element `β` of
  -- `det (ker (f.prodMap g))`.
  obtain ⟨β, hβ, hβ₀⟩ := exists_ιMulti_append_ne_zero f g
  refine TensorProduct.ext' fun b φ ↦ ?_
  obtain ⟨r, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' (V := TauCeti.detLine K (ker (f.prodMap g)))
    _ hβ₀).1 (TauCeti.finrank_detLine K (ker (f.prodMap g))) b
  have h := detLineEquivOfExact_prodMap_tmul_eq_smul f g _ _ hβ φ
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe, ← smul_tmul', LinearEquiv.map_smul, h]
  exact smul_comm _ _ _

end Prod

end LinearMap
