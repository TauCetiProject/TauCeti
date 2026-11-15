/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Pi
public import TauCeti.RepresentationTheory.SymmetricAlgebra.TrivialSummand

/-!
# Polynomial invariants of products of representations

Let `ρ : Representation R G M` and `σ : Representation R H N` be representations of finite groups
`G` and `H`. The product group `G × H` acts on `M × N` by
`Representation.prod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))`.
Under the canonical isomorphism `Sym (M × N) ≃ Sym M ⊗[R] Sym N` (`SymmetricAlgebra.prodEquiv`),
`(g, 1)` acts on the first tensor factor and `(1, h)` on the second.

When `Sym M` and `Sym(N)^H` are flat over `R` (for instance when `M` is free and `Sym(N)^H` is a
polynomial algebra, or over any field), taking `H`-invariants and then `G`-invariants yields an
`R`-algebra equivalence

`Sym (M × N)^(G × H) ≃ₐ[R] Sym(M)^G ⊗[R] Sym(N)^H`.

Consequently, basic invariants of `M` and of `N` combine to form basic invariants of `M × N`. By
induction on a finite index type `α`, basic invariants of a finite family of representations
`ρ a : Representation R (G a) (M a)` of finite groups on free `R`-modules combine via the
coordinate inclusions `M a → ∀ b, M b` to form basic invariants of the coordinatewise product
representation on `∀ b, M b`.

## Main definitions

* `Representation.symmetricAlgebraInvariantsProdEquiv`: the algebra equivalence
  `Sym (M × N)^(G × H) ≃ₐ[R] Sym(M)^G ⊗[R] Sym(N)^H`.

## Main results

* `Representation.bijective_aeval_symmetricAlgebraInvariants_prod`: polynomial generators of
  `Sym(M)^G` and `Sym(N)^H` combine to polynomial generators of `Sym (M × N)^(G × H)`.
* `Representation.bijective_aeval_symmetricAlgebraInvariants_of_equiv`: transport of basic
  polynomial invariants along group, module, and index equivalences.
* `Representation.bijective_aeval_symmetricAlgebraInvariants_pi`: polynomial generators of a finite
  family of representations on free modules combine to polynomial generators of the product
  representation on `∀ a, M a`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. V, §5, no. 2.
* R. Kane, *Reflection Groups and Invariant Theory*, Springer (2001), §16.
-/

public section

open TensorProduct

namespace Representation

section Binary

variable {R G H M N : Type*} [CommRing R] [Group G] [Group H]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (ρ : Representation R G M) (σ : Representation R H N)

private noncomputable abbrev prodMapRep : Representation R (G × H) (M × N) :=
  Representation.prod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

private theorem prodEquiv_symmetricAlgebra_prod_apply (g : G) (h : H)
    (p : SymmetricAlgebra R (M × N)) :
    SymmetricAlgebra.prodEquiv R M N ((prodMapRep ρ σ).symmetricAlgebra (g, h) p) =
      Algebra.TensorProduct.map (SymmetricAlgebra.map R (ρ g)) (SymmetricAlgebra.map R (σ h))
        (SymmetricAlgebra.prodEquiv R M N p) := by
  have hgh : prodMapRep ρ σ (g, h) = (ρ g).prodMap (σ h) := by ext <;> simp [prodMapRep]
  rw [symmetricAlgebra_apply, hgh, SymmetricAlgebra.prodEquiv_map_prodMap]

private theorem prodEquiv_symm_map_val_mem_symmetricAlgebraInvariants
    (x : ρ.symmetricAlgebraInvariants ⊗[R] σ.symmetricAlgebraInvariants) :
    (SymmetricAlgebra.prodEquiv R M N).symm
        (Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
          σ.symmetricAlgebraInvariants.val x) ∈
      (prodMapRep ρ σ).symmetricAlgebraInvariants := by
  refine ((prodMapRep ρ σ).mem_symmetricAlgebraInvariants _).2 fun ⟨g, h⟩ ↦ ?_
  apply (SymmetricAlgebra.prodEquiv R M N).injective
  rw [prodEquiv_symmetricAlgebra_prod_apply, AlgEquiv.apply_symm_apply]
  induction x with
  | add _ _ hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp only [Algebra.TensorProduct.map_tmul, Subalgebra.coe_val,
      ← symmetricAlgebra_apply, (ρ.mem_symmetricAlgebraInvariants a).1 a.2 g,
      (σ.mem_symmetricAlgebraInvariants b).1 b.2 h]

private theorem lTensor_val_eq_algebra_lTensor
    (u : SymmetricAlgebra R M ⊗[R] σ.symmetricAlgebraInvariants) :
    LinearMap.lTensor (SymmetricAlgebra R M) σ.symmetricAlgebraInvariants.val.toLinearMap u =
      Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R M) (SymmetricAlgebra R M)
        σ.symmetricAlgebraInvariants.val u := by
  induction u with | add _ _ ha hb => simp [ha, hb] | tmul => simp

variable [Finite G] [Finite H] [Module.Flat R (SymmetricAlgebra R M)]
  [Module.Flat R σ.symmetricAlgebraInvariants]

private theorem exists_prodEquiv_symm_map_val_eq {p : SymmetricAlgebra R (M × N)}
    (hp : p ∈ (prodMapRep ρ σ).symmetricAlgebraInvariants) :
    ∃ x : ρ.symmetricAlgebraInvariants ⊗[R] σ.symmetricAlgebraInvariants,
      (SymmetricAlgebra.prodEquiv R M N).symm
        (Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
          σ.symmetricAlgebraInvariants.val x) = p := by
  have hpH : p ∈ (Representation.prod (trivial R H M) σ).symmetricAlgebraInvariants := by
    refine ((Representation.prod (trivial R H M) σ).mem_symmetricAlgebraInvariants p).2 fun h ↦ ?_
    have hact : Representation.prod (trivial R H M) σ h = prodMapRep ρ σ (1, h) := by
      ext <;> simp [prodMapRep]
    rw [symmetricAlgebra_apply, hact, ← symmetricAlgebra_apply]
    exact ((prodMapRep ρ σ).mem_symmetricAlgebraInvariants p).1 hp (1, h)
  let y := σ.symmetricAlgebraInvariantsTrivialProdEquiv ⟨p, hpH⟩
  have hy : Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R M) (SymmetricAlgebra R M)
      σ.symmetricAlgebraInvariants.val y = SymmetricAlgebra.prodEquiv R M N p :=
    σ.lTensor_val_symmetricAlgebraInvariantsTrivialProdEquiv ⟨p, hpH⟩
  let c₁ := Algebra.TensorProduct.comm R (SymmetricAlgebra R M) σ.symmetricAlgebraInvariants
  have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := SymmetricAlgebra R M)
    σ.symmetricAlgebraInvariants.val.toLinearMap Subtype.val_injective
  have hc₁y : c₁ y ∈ (ρ.symmetricAlgebra.baseChange σ.symmetricAlgebraInvariants).invariants := by
    refine (mem_invariants _ _).2 fun g ↦ c₁.symm.injective <| hinj ?_
    rw [lTensor_val_eq_algebra_lTensor σ, lTensor_val_eq_algebra_lTensor σ,
      AlgEquiv.symm_apply_apply]
    have hstep :
        Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R M) (SymmetricAlgebra R M)
          σ.symmetricAlgebraInvariants.val
          (c₁.symm ((ρ.symmetricAlgebra.baseChange σ.symmetricAlgebraInvariants) g (c₁ y))) =
        Algebra.TensorProduct.map (SymmetricAlgebra.map R (ρ g)) (.id R _)
          (Algebra.TensorProduct.lTensor (S := SymmetricAlgebra R M) (SymmetricAlgebra R M)
            σ.symmetricAlgebraInvariants.val y) := by
      clear hy
      induction y with | add _ _ hu hv => simp only [map_add, hu, hv] | tmul => simp [c₁]
    rw [hstep, hy]
    have hprod := prodEquiv_symmetricAlgebra_prod_apply ρ σ g 1 p
    rw [((prodMapRep ρ σ).mem_symmetricAlgebraInvariants p).1 hp (g, 1), σ.map_one,
      Module.End.one_eq_id, SymmetricAlgebra.map_id] at hprod
    exact hprod.symm
  obtain ⟨z, hz⟩ := ρ.exists_lTensor_val_eq_of_mem_invariants_baseChange hc₁y
  let c₂ := Algebra.TensorProduct.comm R σ.symmetricAlgebraInvariants ρ.symmetricAlgebraInvariants
  refine ⟨c₂ z, (SymmetricAlgebra.prodEquiv R M N).injective ?_⟩
  rw [AlgEquiv.apply_symm_apply, ← hy, ← c₁.symm_apply_apply y, ← hz]
  clear hz; induction z with | add _ _ hu hv => simp only [map_add, hu, hv] | tmul => simp [c₁, c₂]

omit [Finite G] [Finite H] in
private theorem injective_tensorProduct_map_val :
    Function.Injective
      (Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
        σ.symmetricAlgebraInvariants.val) := fun x y hxy ↦ by
  apply Module.Flat.rTensor_preserves_injective_linearMap
    ρ.symmetricAlgebraInvariants.val.toLinearMap Subtype.val_injective
  apply Module.Flat.lTensor_preserves_injective_linearMap
    σ.symmetricAlgebraInvariants.val.toLinearMap Subtype.val_injective
  have hcomp (u : ρ.symmetricAlgebraInvariants ⊗[R] σ.symmetricAlgebraInvariants) :
      LinearMap.lTensor (SymmetricAlgebra R M) σ.symmetricAlgebraInvariants.val.toLinearMap
        (LinearMap.rTensor σ.symmetricAlgebraInvariants
          ρ.symmetricAlgebraInvariants.val.toLinearMap u) =
      Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
        σ.symmetricAlgebraInvariants.val u := by
    induction u with | add _ _ ha hb => simp only [map_add, ha, hb] | tmul => simp
  rw [hcomp, hcomp, hxy]

/-- **Invariants of a product of representations.** Let finite groups `G` and `H` act on `M` and
`N` via `ρ` and `σ`, with `Sym M` and `Sym(N)^H` flat over `R`. Then the `(G × H)`-invariant
subalgebra of `Sym (M × N)` is canonically `Sym(M)^G ⊗[R] Sym(N)^H`. -/
noncomputable def symmetricAlgebraInvariantsProdEquiv :
    (Representation.prod (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H))).symmetricAlgebraInvariants ≃ₐ[R]
      ρ.symmetricAlgebraInvariants ⊗[R] σ.symmetricAlgebraInvariants :=
  ((AlgEquiv.ofInjective
    ((SymmetricAlgebra.prodEquiv R M N).symm.toAlgHom.comp
      (Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
        σ.symmetricAlgebraInvariants.val))
    ((SymmetricAlgebra.prodEquiv R M N).symm.injective.comp
      (injective_tensorProduct_map_val ρ σ))).trans <|
    Subalgebra.equivOfEq _ _ <| le_antisymm
      (fun _ ⟨x, hx⟩ ↦ hx ▸ prodEquiv_symm_map_val_mem_symmetricAlgebraInvariants ρ σ x)
      fun _ hp ↦ exists_prodEquiv_symm_map_val_eq ρ σ hp).symm

/-- Embedding `Sym(M)^G ⊗[R] Sym(N)^H` into `Sym (M × N)` via
`(symmetricAlgebraInvariantsProdEquiv ρ σ).symm` maps the tensor factors into `Sym M ⊗[R] Sym N`
and applies `(SymmetricAlgebra.prodEquiv R M N).symm`. -/
@[simp]
theorem coe_symmetricAlgebraInvariantsProdEquiv_symm
    (x : ρ.symmetricAlgebraInvariants ⊗[R] σ.symmetricAlgebraInvariants) :
    ((symmetricAlgebraInvariantsProdEquiv ρ σ).symm x : SymmetricAlgebra R (M × N)) =
      (SymmetricAlgebra.prodEquiv R M N).symm
        (Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
          σ.symmetricAlgebraInvariants.val x) :=
  (rfl)

/-- Applying `symmetricAlgebraInvariantsProdEquiv ρ σ` and mapping both tensor factors into
`Sym M` and `Sym N` recovers `SymmetricAlgebra.prodEquiv R M N` on the underlying polynomial. -/
@[simp]
theorem map_val_symmetricAlgebraInvariantsProdEquiv
    (p : (Representation.prod (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H))).symmetricAlgebraInvariants) :
    Algebra.TensorProduct.map ρ.symmetricAlgebraInvariants.val
      σ.symmetricAlgebraInvariants.val (symmetricAlgebraInvariantsProdEquiv ρ σ p) =
      SymmetricAlgebra.prodEquiv R M N p.1 := by
  apply (SymmetricAlgebra.prodEquiv R M N).symm.injective
  rw [AlgEquiv.symm_apply_apply, ← coe_symmetricAlgebraInvariantsProdEquiv_symm,
    AlgEquiv.symm_apply_apply]

omit [Module.Flat R σ.symmetricAlgebraInvariants] in
/-- **Basic invariants of a product of representations.** If `f₁` and `f₂` are polynomial
generators of `Sym(M)^G` and `Sym(N)^H`, with `Sym M` flat over `R`, then pulling `f₁` and `f₂`
back along `inl : M → M × N` and `inr : N → M × N` gives polynomial generators of
`Sym (M × N)^(G × H)`. -/
theorem bijective_aeval_symmetricAlgebraInvariants_prod {κ₁ κ₂ : Type*}
    {f₁ : κ₁ → ρ.symmetricAlgebraInvariants} {f₂ : κ₂ → σ.symmetricAlgebraInvariants}
    (hf₁ : Function.Bijective (MvPolynomial.aeval (R := R) f₁))
    (hf₂ : Function.Bijective (MvPolynomial.aeval (R := R) f₂))
    {F : κ₁ ⊕ κ₂ → (Representation.prod (ρ.comp (MonoidHom.fst G H))
      (σ.comp (MonoidHom.snd G H))).symmetricAlgebraInvariants}
    (hF₁ : ∀ i, (F (.inl i) : SymmetricAlgebra R (M × N)) =
      SymmetricAlgebra.map R (LinearMap.inl R M N) (f₁ i))
    (hF₂ : ∀ j, (F (.inr j) : SymmetricAlgebra R (M × N)) =
      SymmetricAlgebra.map R (LinearMap.inr R M N) (f₂ j)) :
    Function.Bijective (MvPolynomial.aeval (R := R) F) := by
  let e₂ : MvPolynomial κ₂ R ≃ₐ[R] σ.symmetricAlgebraInvariants := AlgEquiv.ofBijective _ hf₂
  have : Module.Free R σ.symmetricAlgebraInvariants := Module.Free.of_equiv e₂.toLinearEquiv
  let e : MvPolynomial (κ₁ ⊕ κ₂) R ≃ₐ[R] (prodMapRep ρ σ).symmetricAlgebraInvariants :=
    (MvPolynomial.tensorEquivSum R κ₁ κ₂ R).symm.trans <|
      (Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hf₁) e₂).trans
      (symmetricAlgebraInvariantsProdEquiv ρ σ).symm
  have he : MvPolynomial.aeval (R := R) F = e.toAlgHom := by
    refine MvPolynomial.algHom_ext fun k ↦ Subtype.ext ?_
    rcases k with i | j
    · have hx : (MvPolynomial.tensorEquivSum R κ₁ κ₂ R).symm (.X (.inl i)) = .X i ⊗ₜ 1 := by
        rw [AlgEquiv.symm_apply_eq, MvPolynomial.tensorEquivSum_X_tmul_one]
      simp [e, e₂, hx, hF₁]
    · have hx : (MvPolynomial.tensorEquivSum R κ₁ κ₂ R).symm (.X (.inr j)) = 1 ⊗ₜ .X j := by
        rw [AlgEquiv.symm_apply_eq, MvPolynomial.tensorEquivSum_one_tmul_X]
      simp [e, e₂, hx, hF₂]
  exact he ▸ e.bijective

end Binary

section Pi

variable {R α : Type*} [CommRing R]

/-- Transport bijectivity of `MvPolynomial.aeval` on `symmetricAlgebraInvariants` along a
group isomorphism, an intertwining linear equivalence, and an index equivalence. -/
theorem bijective_aeval_symmetricAlgebraInvariants_of_equiv {G₁ G₂ M₁ M₂ κ₁ κ₂ : Type*}
    [Group G₁] [Group G₂] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    {ρ₁ : Representation R G₁ M₁} {ρ₂ : Representation R G₂ M₂}
    (φ : G₁ ≃* G₂) (eM : M₁ ≃ₗ[R] M₂) (eκ : κ₁ ≃ κ₂)
    (hint : ∀ g x, eM (ρ₁ g x) = ρ₂ (φ g) (eM x))
    {f₁ : κ₁ → ρ₁.symmetricAlgebraInvariants} {f₂ : κ₂ → ρ₂.symmetricAlgebraInvariants}
    (hf₁ : Function.Bijective (MvPolynomial.aeval (R := R) f₁))
    (hcompat : ∀ k, (f₂ (eκ k) : SymmetricAlgebra R M₂) =
      SymmetricAlgebra.map R eM.toLinearMap (f₁ k)) :
    Function.Bijective (MvPolynomial.aeval (R := R) f₂) := by
  let ρ₂' : Representation R G₁ M₂ := ρ₂.comp φ.toMonoidHom
  have hint₁ : IsIntertwiningMap ρ₁ ρ₂' eM.toLinearMap := ⟨hint⟩
  have hint₂ : IsIntertwiningMap ρ₂' ρ₁ eM.symm.toLinearMap :=
    ⟨fun g y ↦ eM.injective (by simp [ρ₂', hint])⟩
  have hmap : ρ₁.symmetricAlgebraInvariants.map (SymmetricAlgebra.map R eM.toLinearMap) =
      ρ₂.symmetricAlgebraInvariants := by
    rw [map_symmetricAlgebraInvariants_of_leftInverse hint₁ hint₂ eM.apply_symm_apply]
    exact ρ₂.symmetricAlgebraInvariants_comp_of_surjective φ.toMonoidHom φ.surjective
  let eAlg : ρ₁.symmetricAlgebraInvariants ≃ₐ[R] ρ₂.symmetricAlgebraInvariants :=
    (ρ₁.symmetricAlgebraInvariants.equivMapOfInjective (SymmetricAlgebra.map R eM.toLinearMap)
      (SymmetricAlgebra.map_leftInverse R eM.symm_apply_apply).injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  let eTot : MvPolynomial κ₂ R ≃ₐ[R] ρ₂.symmetricAlgebraInvariants :=
    (MvPolynomial.renameEquiv R eκ.symm).trans ((AlgEquiv.ofBijective _ hf₁).trans eAlg)
  have he : MvPolynomial.aeval (R := R) f₂ = eTot.toAlgHom := by
    refine MvPolynomial.algHom_ext fun k₂ ↦ Subtype.ext ?_
    obtain ⟨k₁, rfl⟩ := eκ.surjective k₂
    simp [eTot, eAlg, hcompat]
  exact he ▸ eTot.bijective

private theorem single_mem_symmetricAlgebraInvariants_pi [DecidableEq α]
    {G M : α → Type*} [∀ a, Group (G a)] [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)]
    (ρ : ∀ a, Representation R (G a) (M a)) (a : α)
    {p : SymmetricAlgebra R (M a)} (hp : p ∈ (ρ a).symmetricAlgebraInvariants) :
    SymmetricAlgebra.map R (LinearMap.single R M a) p ∈
      (Representation.pi fun b ↦ (ρ b).comp (Pi.evalMonoidHom G b)).symmetricAlgebraInvariants :=
  map_mem_symmetricAlgebraInvariants
    (ρ := (ρ a).comp (Pi.evalMonoidHom G a))
    (ρ' := Representation.pi fun b ↦ (ρ b).comp (Pi.evalMonoidHom G b))
    ⟨fun _ _ ↦ by
      ext c; by_cases h : c = a
      · subst h; simp [LinearMap.single_apply]
      · simp [h, LinearMap.single_apply]⟩
    (by
      rw [(ρ a).symmetricAlgebraInvariants_comp_of_surjective (Pi.evalMonoidHom G a)
        (Function.surjective_eval a)]
      exact hp)

/-- **Basic invariants of a finite product of representations.** Let `α` be a finite index type,
and for each `a : α` let `G a` be a finite group acting on a free `R`-module `M a` via `ρ a`. If
`f a : κ a → Sym(M a)^(G a)` is a family of polynomial generators for each `a`, then their images
under `LinearMap.single R M a : M a →ₗ[R] ∀ b, M b` form polynomial generators of the invariant
subalgebra of `∀ b, M b` under `∀ b, G b`. -/
theorem bijective_aeval_symmetricAlgebraInvariants_pi [Finite α] [instDec : DecidableEq α]
    {G M κ : α → Type*} [∀ a, Group (G a)] [∀ a, Finite (G a)]
    [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)] [∀ a, Module.Free R (M a)]
    (ρ : ∀ a, Representation R (G a) (M a))
    {f : (a : α) → κ a → (ρ a).symmetricAlgebraInvariants}
    (hf : ∀ a, Function.Bijective (MvPolynomial.aeval (R := R) (f a)))
    {F : (Σ a, κ a) →
      (Representation.pi fun a ↦ (ρ a).comp (Pi.evalMonoidHom G a)).symmetricAlgebraInvariants}
    (hF : ∀ a k, (F ⟨a, k⟩ : SymmetricAlgebra R (∀ b, M b)) =
      SymmetricAlgebra.map R (LinearMap.single R M a) (f a k)) :
    Function.Bijective (MvPolynomial.aeval (R := R) F) := by
  revert hF instDec
  induction α using Finite.induction_empty_option with
  | @of_equiv α₁ α₂ eα ih =>
    intro _ hF
    let _ : DecidableEq α₁ := Classical.decEq α₁
    let G' b := G (eα b)
    let M' b := M (eα b)
    let ρ' b := ρ (eα b)
    let ρPi' := Representation.pi fun b : α₁ ↦ (ρ' b).comp (Pi.evalMonoidHom G' b)
    let ψ : (∀ a, G a) ≃* (∀ b, G' b) :=
      { toEquiv := Equiv.piCongrLeft' G eα.symm, map_mul' := fun _ _ ↦ rfl }
    let ψM : (∀ a, M a) ≃ₗ[R] (∀ b, M' b) := LinearEquiv.piCongrLeft' R M eα.symm
    let F' : (Σ b, κ (eα b)) → ρPi'.symmetricAlgebraInvariants := fun ⟨b, k⟩ ↦
      ⟨SymmetricAlgebra.map R (LinearMap.single R M' b) (f (eα b) k),
        single_mem_symmetricAlgebraInvariants_pi ρ' b (f (eα b) k).2⟩
    refine bijective_aeval_symmetricAlgebraInvariants_of_equiv ψ.symm ψM.symm
      (Equiv.sigmaCongrLeft eα) (fun g x ↦ ?_)
      (ih ρ' (fun b ↦ hf (eα b)) (F := F') (fun _ _ ↦ rfl)) fun ⟨b, k⟩ ↦ ?_
    · obtain ⟨g₂, rfl⟩ := ψ.surjective g
      obtain ⟨x₂, rfl⟩ := ψM.surjective x
      apply ψM.injective
      rw [ψ.symm_apply_apply, ψM.apply_symm_apply, ψM.symm_apply_apply]
      ext b
      have hψ : ψ g₂ b = g₂ (eα b) := rfl
      have hψM : ψM x₂ b = x₂ (eα b) := rfl
      simp [ψM, ρPi', G', M', ρ', hψ, hψM]
    · change (F ⟨eα b, k⟩).1 = _
      rw [hF (eα b) k]
      change _ = SymmetricAlgebra.map R ψM.symm.toLinearMap
        (SymmetricAlgebra.map R (LinearMap.single R M' b) (f (eα b) k))
      rw [← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map]
      refine DFunLike.congr_fun (congrArg (SymmetricAlgebra.map R) (LinearMap.ext fun m ↦ ?_)) _
      apply ψM.injective
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ψM.apply_symm_apply]
      ext c; by_cases hcb : c = b
      · subst hcb; simp [ψM, LinearMap.single_apply]
      · simp [ψM, hcb, eα.injective.eq_iff, LinearMap.single_apply]
  | h_empty =>
    intro _ _
    let eSym : SymmetricAlgebra R (∀ a : PEmpty, M a) ≃ₐ[R] R :=
      (SymmetricAlgebra.equivMvPolynomial (Module.Basis.empty _)).trans
        (MvPolynomial.isEmptyAlgEquiv R Empty)
    let S := (Representation.pi fun a : PEmpty ↦
      (ρ a).comp (Pi.evalMonoidHom G a)).symmetricAlgebraInvariants
    let inv : S →ₐ[R] MvPolynomial (Σ a : PEmpty, κ a) R :=
      (MvPolynomial.isEmptyAlgEquiv R _).symm.toAlgHom.comp (eSym.toAlgHom.comp S.val)
    have hleft : inv.comp (MvPolynomial.aeval (R := R) F) = AlgHom.id R _ :=
      MvPolynomial.algHom_ext fun x ↦ nomatch x.1
    refine Function.bijective_iff_has_inverse.mpr ⟨inv, fun p ↦ congr($hleft p), fun y ↦
      Subtype.ext <| eSym.injective ?_⟩
    have hinv : inv y = algebraMap R _ (eSym y.1) := by simp [inv]
    rw [hinv, AlgHom.commutes]
    exact (eSym.toAlgHom.comp S.val).commutes (eSym y.1)
  | @h_option α _ ih =>
    intro _ hF
    let _ : DecidableEq α := Classical.decEq α
    let G' b := G (some b)
    let M' b := M (some b)
    let ρTail := Representation.pi fun a : α ↦ (ρ (some a)).comp (Pi.evalMonoidHom G' a)
    let FTail : (Σ a : α, κ (some a)) → ρTail.symmetricAlgebraInvariants := fun ⟨a, k⟩ ↦
      ⟨SymmetricAlgebra.map R (LinearMap.single R M' a) (f (some a) k),
        single_mem_symmetricAlgebraInvariants_pi (fun b ↦ ρ (some b)) a (f (some a) k).2⟩
    let ρProd := Representation.prod
      ((ρ none).comp (MonoidHom.fst (G none) (∀ a, G' a)))
      (ρTail.comp (MonoidHom.snd (G none) (∀ a, G' a)))
    let FProd : κ none ⊕ (Σ a, κ (some a)) → ρProd.symmetricAlgebraInvariants :=
      Sum.elim
        (fun k ↦ ⟨SymmetricAlgebra.map R (LinearMap.inl R (M none) (∀ a, M' a)) (f none k),
          map_mem_symmetricAlgebraInvariants (ρ := (ρ none).comp (MonoidHom.fst _ _)) (ρ' := ρProd)
            ⟨fun _ _ ↦ by simp [ρProd, M']⟩ (by
              rw [(ρ none).symmetricAlgebraInvariants_comp_of_surjective _ Prod.fst_surjective]
              exact (f none k).2)⟩)
        (fun x ↦ ⟨SymmetricAlgebra.map R (LinearMap.inr R (M none) (∀ a, M' a)) (FTail x),
          map_mem_symmetricAlgebraInvariants (ρ := ρTail.comp (MonoidHom.snd _ _)) (ρ' := ρProd)
            ⟨fun _ _ ↦ by simp [ρProd, M']⟩ (by
              rw [ρTail.symmetricAlgebraInvariants_comp_of_surjective _ Prod.snd_surjective]
              exact (FTail x).2)⟩)
    have hfProd := bijective_aeval_symmetricAlgebraInvariants_prod (ρ none) ρTail (hf none)
      (ih (fun a ↦ ρ (some a)) (fun a ↦ hf (some a)) (F := FTail) (fun _ _ ↦ rfl))
      (F := FProd) (fun _ ↦ rfl) (fun _ ↦ rfl)
    let φ : (G none × ∀ a, G' a) ≃* ∀ o, G o :=
      { toFun := fun x ↦ Option.rec x.1 x.2, invFun := fun g ↦ (g none, fun a ↦ g (some a)),
        left_inv := fun ⟨_, _⟩ ↦ rfl, right_inv := fun _ ↦ funext fun o ↦ by cases o <;> rfl,
        map_mul' := fun _ _ ↦ funext fun o ↦ by cases o <;> rfl }
    let eM : (M none × ∀ a, M' a) ≃ₗ[R] ∀ o, M o :=
      { toFun := fun x ↦ Option.rec x.1 x.2, invFun := fun m ↦ (m none, fun a ↦ m (some a)),
        map_add' := fun _ _ ↦ funext fun o ↦ by cases o <;> rfl,
        map_smul' := fun _ _ ↦ funext fun o ↦ by cases o <;> rfl,
        left_inv := fun ⟨_, _⟩ ↦ rfl, right_inv := fun _ ↦ funext fun o ↦ by cases o <;> rfl }
    let eκ : (κ none ⊕ Σ a, κ (some a)) ≃ Σ o, κ o :=
      { toFun := Sum.elim (⟨none, ·⟩) fun ⟨a, k⟩ ↦ ⟨some a, k⟩,
        invFun := fun ⟨o, k⟩ ↦ match o with | none => .inl k | some a => .inr ⟨a, k⟩,
        left_inv := fun x ↦ by rcases x with _ | ⟨_, _⟩ <;> rfl,
        right_inv := fun ⟨o, _⟩ ↦ by cases o <;> rfl }
    refine bijective_aeval_symmetricAlgebraInvariants_of_equiv φ eM eκ
      (fun ⟨_, _⟩ ⟨_, _⟩ ↦ by ext o; cases o <;> simp [φ, eM, ρProd, ρTail, G', M'])
      hfProd fun x ↦ ?_
    rcases x with k | ⟨a, k⟩
    · change (F ⟨none, k⟩).1 = _
      rw [hF none k]
      change _ = SymmetricAlgebra.map R eM.toLinearMap
        (SymmetricAlgebra.map R (LinearMap.inl R (M none) (∀ b, M' b)) (f none k))
      rw [← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map]
      exact DFunLike.congr_fun (congrArg (SymmetricAlgebra.map R)
        (by ext _ o; cases o <;> simp [eM, M', LinearMap.single_apply])) _
    · change (F ⟨some a, k⟩).1 = _
      rw [hF (some a) k]
      change _ = SymmetricAlgebra.map R eM.toLinearMap
        (SymmetricAlgebra.map R (LinearMap.inr R (M none) (∀ b, M' b))
          (SymmetricAlgebra.map R (LinearMap.single R M' a) (f (some a) k)))
      rw [← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map,
        ← AlgHom.comp_apply, SymmetricAlgebra.map_comp_map]
      refine DFunLike.congr_fun (congrArg (SymmetricAlgebra.map R) (by ext _ o; cases o with
        | none => simp [eM, M', LinearMap.single_apply]
        | some c =>
          by_cases h : c = a
          · subst h; simp [eM, M', LinearMap.single_apply]
          · simp [eM, M', h, LinearMap.single_apply])) _

end Pi

end Representation
