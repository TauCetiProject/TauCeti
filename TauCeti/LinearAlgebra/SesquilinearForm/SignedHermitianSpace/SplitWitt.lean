/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.PairExtension
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Split
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.WittDecomposition

/-!
# Witt's theorems over the split quadratic algebra `F × F`

Let `F` be a field and `E = F × F` with the involution `σ (a, b) = (b, a)`. A finite free
`ε`-hermitian space `(V, h)` over `E` is isometric to `Eⁿ` with the form
`h a b = ∑ σ (a i) * (ε, 1) * b i`
(`TauCeti.SignedHermitianSpace.exists_linearEquiv_form_eq_sum_split`).
Writing `a = (a₁, a₂)` with `a₁, a₂ ∈ Fⁿ`, this form is `(ε a₂ ⬝ b₁, a₁ ⬝ b₂)`: the two halves
`Fⁿ × 0` and `0 × Fⁿ` are totally isotropic and put in duality by the dot product, and an
isometry of `V` is a pair `(g₁, g₂)` of automorphisms of `Fⁿ` with `g₂ w ⬝ g₁ v = w ⬝ v`. This
file proves:

* **Witt extension over `F × F`**: every injective isometry from a submodule `W` of `V` into `V`
  extends to an element of the unitary group `U(V)`. No freeness is required of `W`: a submodule
  of `V` is `W₁ × W₂` for two subspaces of `Fⁿ`, and the isometry is a pair of injections
  compatible with the dot product, which extends by
  `LinearMap.BilinForm.exists_linearEquiv_pair_extend`.
* **Witt decomposition over `F × F`**: the Witt index of a space of rank `n` is `⌊n / 2⌋`, the
  space is `H^⌊n/2⌋ ⊥ A` for every space `A` of rank `n % 2`, and a space is anisotropic exactly
  when its rank is at most one. The anisotropic part is thus `0` or the line `⟨(ε, 1)⟩`, which
  for `ε = 1` is the standard line `⟨1⟩`.

## Main statements

* `TauCeti.SignedHermitianSpace.exists_mem_isometryGroup_extend_split`: Witt extension.
* `TauCeti.SignedHermitianSpace.wittIndex_split`: the Witt index is `⌊n / 2⌋`.
* `TauCeti.SignedHermitianSpace.equivalent_hyperbolic_prod_split`: the Witt decomposition.
* `TauCeti.SignedHermitianSpace.anisotropic_split_iff`: anisotropic spaces have rank at most one.

## References

* W. Scharlau, *Quadratic and Hermitian Forms*, Grundlehren der mathematischen Wissenschaften
  270, Springer (1985), Chapter 7.
-/

public section

open Module

namespace TauCeti

namespace SignedHermitianSpace

variable {F : Type*} [Field F] {σ : F × F →+* F × F} {ε : ℤˣ}

/-! ### The model space `(F × F)ⁿ` -/

section Model

variable {n : ℕ}

/-- The first components `a₁` of `a : (F × F)ⁿ`. -/
private def fst₁ : (Fin n → F × F) →ₗ[F] Fin n → F :=
  LinearMap.pi fun i ↦ LinearMap.fst F F F ∘ₗ LinearMap.proj i

/-- The second components `a₂` of `a : (F × F)ⁿ`. -/
private def snd₁ : (Fin n → F × F) →ₗ[F] Fin n → F :=
  LinearMap.pi fun i ↦ LinearMap.snd F F F ∘ₗ LinearMap.proj i

/-- The vector `(u, 0)` of `(F × F)ⁿ`. -/
private def inl₁ : (Fin n → F) →ₗ[F] Fin n → F × F :=
  LinearMap.pi fun i ↦ LinearMap.inl F F F ∘ₗ LinearMap.proj i

/-- The vector `(0, u)` of `(F × F)ⁿ`. -/
private def inr₁ : (Fin n → F) →ₗ[F] Fin n → F × F :=
  LinearMap.pi fun i ↦ LinearMap.inr F F F ∘ₗ LinearMap.proj i

private theorem inl₁_apply (u : Fin n → F) (i : Fin n) : inl₁ u i = (u i, 0) := rfl
private theorem inr₁_apply (u : Fin n → F) (i : Fin n) : inr₁ u i = (0, u i) := rfl
private theorem fst₁_apply (a : Fin n → F × F) (i : Fin n) : fst₁ a i = (a i).1 := rfl
private theorem snd₁_apply (a : Fin n → F × F) (i : Fin n) : snd₁ a i = (a i).2 := rfl

private theorem fst₁_inl₁ (u : Fin n → F) : fst₁ (inl₁ u) = u := rfl
private theorem snd₁_inl₁ (u : Fin n → F) : snd₁ (inl₁ u) = 0 := rfl
private theorem fst₁_inr₁ (u : Fin n → F) : fst₁ (inr₁ u) = 0 := rfl
private theorem snd₁_inr₁ (u : Fin n → F) : snd₁ (inr₁ u) = u := rfl

private theorem inl₁_add_inr₁ (a : Fin n → F × F) : inl₁ (fst₁ a) + inr₁ (snd₁ a) = a :=
  funext fun i ↦ Prod.ext (by simp [inl₁_apply, inr₁_apply, fst₁_apply])
    (by simp [inl₁_apply, inr₁_apply, snd₁_apply])

private theorem smul_eq_inl₁ (a : Fin n → F × F) : ((1, 0) : F × F) • a = inl₁ (fst₁ a) :=
  funext fun i ↦ Prod.ext (by simp [inl₁_apply, fst₁_apply]) (by simp [inl₁_apply])

private theorem smul_eq_inr₁ (a : Fin n → F × F) : ((0, 1) : F × F) • a = inr₁ (snd₁ a) :=
  funext fun i ↦ Prod.ext (by simp [inr₁_apply]) (by simp [inr₁_apply, snd₁_apply])

private theorem fst₁_smul (c : F × F) (a : Fin n → F × F) : fst₁ (c • a) = c.1 • fst₁ a := rfl
private theorem snd₁_smul (c : F × F) (a : Fin n → F × F) : snd₁ (c • a) = c.2 • snd₁ a := rfl

/-- The form of the model: `∑ σ (a i) * (ε, 1) * b i = (ε a₂ ⬝ b₁, a₁ ⬝ b₂)`. -/
private theorem sum_split_eq (hσ : ∀ x, σ x = x.swap) (a b : Fin n → F × F) :
    ∑ i, σ (a i) * (((ε : ℤ) : F), 1) * b i =
      (((ε : ℤ) : F) * (snd₁ a ⬝ᵥ fst₁ b), fst₁ a ⬝ᵥ snd₁ b) := by
  ext <;> simp only [hσ, Prod.fst_sum, Prod.snd_sum, Prod.fst_mul, Prod.snd_mul, Prod.fst_swap,
    Prod.snd_swap, dotProduct, fst₁_apply, snd₁_apply, Finset.mul_sum] <;>
    exact Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The pair `(g₁, g₂)` of automorphisms of `Fⁿ`, acting on `(F × F)ⁿ` componentwise. -/
private def splitMap (g₁ g₂ : (Fin n → F) ≃ₗ[F] Fin n → F) :
    (Fin n → F × F) ≃ₗ[F × F] Fin n → F × F where
  toFun a := inl₁ (g₁ (fst₁ a)) + inr₁ (g₂ (snd₁ a))
  invFun a := inl₁ (g₁.symm (fst₁ a)) + inr₁ (g₂.symm (snd₁ a))
  map_add' a b := by simp only [map_add]; abel
  map_smul' c a := funext fun i ↦ Prod.ext
    (by simp [inl₁_apply, inr₁_apply, fst₁_smul])
    (by simp [inl₁_apply, inr₁_apply, snd₁_smul])
  left_inv a := by
    simp only [map_add, fst₁_inl₁, fst₁_inr₁, snd₁_inl₁, snd₁_inr₁, add_zero, zero_add,
      LinearEquiv.symm_apply_apply]
    exact inl₁_add_inr₁ a
  right_inv a := by
    simp only [map_add, fst₁_inl₁, fst₁_inr₁, snd₁_inl₁, snd₁_inr₁, add_zero, zero_add,
      LinearEquiv.apply_symm_apply]
    exact inl₁_add_inr₁ a

private theorem fst₁_splitMap (g₁ g₂ : (Fin n → F) ≃ₗ[F] Fin n → F) (a : Fin n → F × F) :
    fst₁ (splitMap g₁ g₂ a) = g₁ (fst₁ a) := by
  simp [splitMap, fst₁_inl₁, fst₁_inr₁]

private theorem snd₁_splitMap (g₁ g₂ : (Fin n → F) ≃ₗ[F] Fin n → F) (a : Fin n → F × F) :
    snd₁ (splitMap g₁ g₂ a) = g₂ (snd₁ a) := by
  simp [splitMap, snd₁_inl₁, snd₁_inr₁]

/-- A linear map from a submodule of `(F × F)ⁿ` sends `(u, 0)` to a vector `(v, 0)`. -/
private theorem apply_inl₁ {W : Submodule (F × F) (Fin n → F × F)}
    (f : W →ₗ[F × F] Fin n → F × F) {u : Fin n → F} (hu : inl₁ u ∈ W) :
    f ⟨inl₁ u, hu⟩ = inl₁ (fst₁ (f ⟨inl₁ u, hu⟩)) :=
  calc f ⟨inl₁ u, hu⟩ = ((1, 0) : F × F) • f ⟨inl₁ u, hu⟩ := by
        rw [← map_smul]
        exact congrArg f (Subtype.ext (by simp [smul_eq_inl₁, fst₁_inl₁]))
    _ = _ := smul_eq_inl₁ _

/-- A linear map from a submodule of `(F × F)ⁿ` sends `(0, u)` to a vector `(0, v)`. -/
private theorem apply_inr₁ {W : Submodule (F × F) (Fin n → F × F)}
    (f : W →ₗ[F × F] Fin n → F × F) {u : Fin n → F} (hu : inr₁ u ∈ W) :
    f ⟨inr₁ u, hu⟩ = inr₁ (snd₁ (f ⟨inr₁ u, hu⟩)) :=
  calc f ⟨inr₁ u, hu⟩ = ((0, 1) : F × F) • f ⟨inr₁ u, hu⟩ := by
        rw [← map_smul]
        exact congrArg f (Subtype.ext (by simp [smul_eq_inr₁, snd₁_inr₁]))
    _ = _ := smul_eq_inr₁ _

/-- A pair `(g₁, g₂)` with `g₂ w ⬝ g₁ v = w ⬝ v` preserves the model form. -/
private theorem sum_splitMap (hσ : ∀ x, σ x = x.swap) {g₁ g₂ : (Fin n → F) ≃ₗ[F] Fin n → F}
    (hg : ∀ w v, g₂ w ⬝ᵥ g₁ v = w ⬝ᵥ v) (a b : Fin n → F × F) :
    ∑ i, σ (splitMap g₁ g₂ a i) * (((ε : ℤ) : F), 1) * splitMap g₁ g₂ b i =
      ∑ i, σ (a i) * (((ε : ℤ) : F), 1) * b i := by
  rw [sum_split_eq hσ, sum_split_eq hσ, fst₁_splitMap, fst₁_splitMap, snd₁_splitMap,
    snd₁_splitMap, dotProduct_comm (g₁ _), hg, hg, dotProduct_comm (snd₁ b)]

/-- **Witt extension in the model `(F × F)ⁿ`.** An injective linear map from a submodule `W` of
`(F × F)ⁿ` preserving the model form extends to an automorphism preserving it. -/
private theorem exists_linearEquiv_extend_model (hσ : ∀ x, σ x = x.swap)
    {W : Submodule (F × F) (Fin n → F × F)} (f : W →ₗ[F × F] Fin n → F × F)
    (hf : Function.Injective f)
    (hff : ∀ x y : W, ∑ i, σ (f x i) * (((ε : ℤ) : F), 1) * f y i =
      ∑ i, σ ((x : Fin n → F × F) i) * (((ε : ℤ) : F), 1) * (y : Fin n → F × F) i) :
    ∃ G : (Fin n → F × F) ≃ₗ[F × F] Fin n → F × F,
      (∀ a b, ∑ i, σ (G a i) * (((ε : ℤ) : F), 1) * G b i =
        ∑ i, σ (a i) * (((ε : ℤ) : F), 1) * b i) ∧ ∀ x : W, G x = f x := by
  -- `W` is `W₁ × W₂` for two subspaces of `Fⁿ`, and `f` is a pair `(f₁, f₂)`.
  let W₁ : Submodule F (Fin n → F) := (W.restrictScalars F).comap inl₁
  let W₂ : Submodule F (Fin n → F) := (W.restrictScalars F).comap inr₁
  have hW₁ (x : W) : fst₁ (x : Fin n → F × F) ∈ W₁ := by
    change inl₁ _ ∈ W
    rw [← smul_eq_inl₁]
    exact W.smul_mem _ x.property
  have hW₂ (x : W) : snd₁ (x : Fin n → F × F) ∈ W₂ := by
    change inr₁ _ ∈ W
    rw [← smul_eq_inr₁]
    exact W.smul_mem _ x.property
  let f₁ : W₁ →ₗ[F] Fin n → F :=
    fst₁ ∘ₗ f.restrictScalars F ∘ₗ inl₁.restrict (q := W.restrictScalars F) fun _ hu ↦ hu
  let f₂ : W₂ →ₗ[F] Fin n → F :=
    snd₁ ∘ₗ f.restrictScalars F ∘ₗ inr₁.restrict (q := W.restrictScalars F) fun _ hu ↦ hu
  have hf₁ (u : W₁) : f ⟨inl₁ u, u.property⟩ = inl₁ (f₁ u) := apply_inl₁ f u.property
  have hf₂ (u : W₂) : f ⟨inr₁ u, u.property⟩ = inr₁ (f₂ u) := apply_inr₁ f u.property
  have hinj₁ : Function.Injective f₁ := fun u v huv ↦ by
    have := hf (show f ⟨inl₁ u, u.property⟩ = f ⟨inl₁ v, v.property⟩ by
      rw [hf₁, hf₁, huv])
    exact Subtype.ext (by
      simpa [fst₁_inl₁] using congrArg (fun w : W ↦ fst₁ (w : Fin n → F × F)) this)
  have hinj₂ : Function.Injective f₂ := fun u v huv ↦ by
    have := hf (show f ⟨inr₁ u, u.property⟩ = f ⟨inr₁ v, v.property⟩ by
      rw [hf₂, hf₂, huv])
    exact Subtype.ext (by
      simpa [snd₁_inr₁] using congrArg (fun w : W ↦ snd₁ (w : Fin n → F × F)) this)
  -- The pair is compatible with the dot product.
  have hε : ((ε : ℤ) : F) ≠ 0 := by rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have hcompat (a : W₁) (b : W₂) : f₂ b ⬝ᵥ f₁ a = (b : Fin n → F) ⬝ᵥ a := by
    have := congrArg Prod.fst (hff ⟨inr₁ b, b.property⟩ ⟨inl₁ a, a.property⟩)
    rw [hf₁, hf₂, sum_split_eq hσ, sum_split_eq hσ] at this
    simpa [snd₁_inr₁, fst₁_inl₁, hε] using this
  let B : LinearMap.BilinForm F (Fin n → F) := dotProductBilin F F
  have hB : B.Nondegenerate :=
    ⟨fun v hv ↦ funext fun i ↦ by simpa [B] using hv (Pi.single i 1),
      fun w hw ↦ funext fun i ↦ by simpa [B] using hw (Pi.single i 1)⟩
  obtain ⟨g₁, g₂, hg₁, hg₂, hg⟩ :=
    LinearMap.BilinForm.exists_linearEquiv_pair_extend hB f₁ f₂ hinj₁ hinj₂ hcompat
  refine ⟨splitMap g₁ g₂, sum_splitMap hσ fun w v ↦ hg w v, fun x ↦ ?_⟩
  · have hx : x = ⟨inl₁ (fst₁ (x : Fin n → F × F)), hW₁ x⟩ +
        ⟨inr₁ (snd₁ (x : Fin n → F × F)), hW₂ x⟩ := Subtype.ext (inl₁_add_inr₁ _).symm
    conv_rhs => rw [hx, map_add, hf₁ ⟨_, hW₁ x⟩, hf₂ ⟨_, hW₂ x⟩]
    simp [splitMap, ← hg₁, ← hg₂]

end Model

/-! ### Witt extension -/

variable {V : Type*} [AddCommGroup V] [Module (F × F) V] [Module.Free (F × F) V]
  [Module.Finite (F × F) V] (H : SignedHermitianSpace (F × F) V σ ε)

/-- **Witt's extension theorem over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of
`F × F`. On a finite free `ε`-hermitian space over `F × F`, every injective isometry from a
submodule `W` into the space extends to an element of the unitary group. -/
theorem exists_mem_isometryGroup_extend_split (hσ : ∀ x, σ x = x.swap) {W : Submodule (F × F) V}
    (f : W →ₗ[F × F] V) (hf : Function.Injective f)
    (hff : ∀ x y, H.form (f x) (f y) = H.form x y) :
    ∃ g ∈ H.form.isometryGroup, ∀ x : W, g x = f x := by
  obtain ⟨T, hT⟩ := H.exists_linearEquiv_form_eq_sum_split hσ rfl
  -- Transport `W` and `f` to the model `(F × F)ⁿ` along `T`.
  let W' := W.comap T.toLinearMap
  let f' : W' →ₗ[F × F] _ := T.symm.toLinearMap ∘ₗ f ∘ₗ
    T.toLinearMap.restrict (p := W') (q := W) fun _ hx ↦ hx
  have hf' (x : W') : T (f' x) = f ⟨T x, x.property⟩ := T.apply_symm_apply _
  obtain ⟨G, hG, hGf⟩ := exists_linearEquiv_extend_model (ε := ε) hσ f'
    (fun x y hxy ↦ Subtype.ext (T.injective (congrArg Subtype.val
      (hf ((hf' x).symm.trans ((congrArg T hxy).trans (hf' y)))))))
    fun x y ↦ by rw [← hT, ← hT, hf', hf', hff]
  refine ⟨T.symm ≪≫ₗ G ≪≫ₗ T, LinearMap.mem_isometryGroup_iff.2 fun v w ↦ ?_, fun x ↦ ?_⟩
  · simp only [LinearEquiv.trans_apply, hT, hG]
    rw [← hT, T.apply_symm_apply, T.apply_symm_apply]
  · have hx : T.symm x ∈ W' := by simp [W']
    have := hGf ⟨T.symm x, hx⟩
    simp only [LinearEquiv.trans_apply]
    rw [this, hf']
    simp

/-! ### Witt decomposition -/

/-- The Gram-diagonal line `⟨(ε, 1)⟩` has `σ (ε, 1) = ε • (ε, 1)` for the swap `σ`. -/
private theorem apply_split_unit (hσ : ∀ x, σ x = x.swap) :
    σ (((ε : ℤ) : F), 1) = ε • (((ε : ℤ) : F), (1 : F)) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> ext <;> simp [hσ]

/-- A space over `F × F` of rank at most one is anisotropic. -/
private theorem anisotropic_of_finrank_le_one (hσ : ∀ x, σ x = x.swap)
    (h : finrank (F × F) V ≤ 1) : H.Anisotropic := by
  obtain ⟨T, hT⟩ := H.exists_linearEquiv_form_eq_sum_split hσ rfl
  rw [anisotropic_iff]
  intro x hiso
  obtain ⟨hxx, hx⟩ : _ ∧ _ := hiso
  obtain ⟨a, rfl⟩ := T.surjective x
  have hsub : Subsingleton (Fin (finrank (F × F) V)) := Fin.subsingleton_iff_le_one.2 h
  rw [hT, sum_split_eq hσ] at hxx
  have h₂ : fst₁ a ⬝ᵥ snd₁ a = 0 := congrArg Prod.snd hxx
  -- Either every first component vanishes, or the (single) second component does.
  by_cases h₁ : ∀ i, (a i).1 = 0
  · refine one_ne_zero (congrArg Prod.fst (hx ((1, 0) : F × F) ?_))
    rw [← map_smul, smul_eq_inl₁]
    simp [show fst₁ a = 0 from funext h₁]
  · push Not at h₁
    obtain ⟨i₀, hi₀⟩ := h₁
    have hb : snd₁ a = 0 := funext fun i ↦ by
      obtain rfl := Subsingleton.elim i i₀
      have : (a i).1 * (a i).2 = 0 := by
        simpa [dotProduct, Fintype.sum_subsingleton _ i, fst₁_apply, snd₁_apply] using h₂
      simpa [snd₁_apply, hi₀] using this
    refine one_ne_zero (congrArg Prod.snd (hx ((0, 1) : F × F) ?_))
    rw [← map_smul, smul_eq_inr₁, hb]
    simp

omit [Module.Free (F × F) V] [Module.Finite (F × F) V] in
/-- The swap is an involution. -/
private theorem ringHomInvPair_split (hσ : ∀ x, σ x = x.swap) : RingHomInvPair σ σ :=
  ⟨RingHom.ext fun x ↦ by simp [hσ], RingHom.ext fun x ↦ by simp [hσ]⟩

/-- **Witt decomposition over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of
`F × F`. A finite free `ε`-hermitian space `V` of rank `n` over `F × F` is isometric to
`H^⌊n/2⌋ ⊥ A` for every space `A` of rank `n % 2`. -/
theorem equivalent_hyperbolic_prod_split [RingHomInvPair σ σ] (hσ : ∀ x, σ x = x.swap)
    {V' : Type*} [AddCommGroup V'] [Module (F × F) V'] [Module.Free (F × F) V']
    [Module.Finite (F × F) V'] (H' : SignedHermitianSpace (F × F) V' σ ε)
    (h : finrank (F × F) V' = finrank (F × F) V % 2) :
    Equivalent H ((hyperbolic (F × F) σ ε (Fin (finrank (F × F) V / 2))).prod H') :=
  H.equivalent_of_finrank_eq_split hσ _ (by simp [finrank_prod, h]; lia)

/-- **The Witt index over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of `F × F`. A
finite free `ε`-hermitian space of rank `n` over `F × F` has Witt index `⌊n / 2⌋`. -/
theorem wittIndex_split (hσ : ∀ x, σ x = x.swap) :
    H.wittIndex = finrank (F × F) V / 2 := by
  have := ringHomInvPair_split hσ
  refine le_antisymm (by have := H.two_mul_wittIndex_le_finrank; lia) ?_
  -- Compare with `H^⌊n/2⌋ ⊥ ⟨(ε, 1)⟩^(n % 2)`.
  let A := diagonal σ ε (fun _ : Fin (finrank (F × F) V % 2) ↦ (((ε : ℤ) : F), (1 : F)))
    (fun _ ↦ apply_split_unit hσ) fun _ ↦ IsUnit.mem_nonZeroDivisors
      (Prod.isUnit_iff.2 ⟨ε.isUnit.map (Int.castRingHom F), isUnit_one⟩)
  rw [(H.equivalent_hyperbolic_prod_split hσ A (by simp)).wittIndex_eq]
  simpa using card_le_wittIndex_hyperbolic_prod (K := F × F) (σ := σ) (ε := ε)
    (Fin (finrank (F × F) V / 2)) A

/-- **Anisotropic spaces over `F × F`.** Let `σ` be the involution `(a, b) ↦ (b, a)` of
`F × F`. A finite free `ε`-hermitian space over `F × F` is anisotropic exactly when its rank is at
most one. -/
theorem anisotropic_split_iff (hσ : ∀ x, σ x = x.swap) :
    H.Anisotropic ↔ finrank (F × F) V ≤ 1 := by
  have := ringHomInvPair_split hσ
  refine ⟨fun h ↦ ?_, H.anisotropic_of_finrank_le_one hσ⟩
  by_contra hV
  obtain ⟨x, y, hxy⟩ := H.exists_isHyperbolicFrame_wittIndex
  have := H.wittIndex_split hσ
  exact (anisotropic_iff.1 h) _ (hxy.isIsotropic_left ⟨0, by lia⟩)

end SignedHermitianSpace

end TauCeti
