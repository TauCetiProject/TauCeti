/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.QuantumTorus.Basic

/-!
# Faithful based charts

A based chart is a family of units with the normalized quantum-torus multiplication
rule whose values are linearly independent over the scalar semiring. Its ambient
algebra can be noncommutative and need not be a division ring. Faithfulness is
separate from any requirement that the chart generate the ambient algebra.

`BasedChart.eval` and `BasedChart.ofInjective` convert between charts and injective
algebra maps from the based quantum torus, with `BasedChart.evalEquiv` identifying
these two presentations. `BasedChart.map` transports charts along injective ambient
algebra maps, and `BasedChart.comap` pulls them back along injective lattice maps
preserving the integral form. Coordinates in any lattice basis determine a chart, and
`BasedChart.untwistedEquiv` recovers ordinary Laurent charts when the twists are one.

## References

* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Advances in Mathematics
  195 (2005), §4. A chart here need not generate its ambient algebra, unlike a
  toric frame in Definition 4.3.
-/

public section

namespace TauCeti

/-- A faithful family of normalized monomials in an ambient algebra. The form is
usually alternating; the multiplication rule and linear independence make sense
for any integral bilinear form. -/
structure BasedChart {R L : Type*} [CommSemiring R] [AddCommGroup L]
    (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (B : Type*) [Semiring B] [Algebra R B] where
  /-- The normalized monomials, as units of the ambient algebra. -/
  monomial : L → Bˣ
  /-- The monomial with zero exponent is one. -/
  monomial_zero : monomial 0 = 1
  /-- The normalized multiplication rule. -/
  monomial_mul (a b : L) : monomial a * monomial b =
    Units.map (algebraMap R B) (u ^ (Λ a b)) * monomial (a + b)
  /-- Faithfulness of finite scalar combinations of normalized monomials. -/
  linearIndependent : LinearIndependent R (fun a ↦ (monomial a : B))

namespace BasedChart

variable {R L B C D : Type*} [CommSemiring R] [AddCommGroup L]
  [Semiring B] [Algebra R B] [Semiring C] [Algebra R C] [Semiring D] [Algebra R D]
  {u : Rˣ} {Λ : LinearMap.BilinForm ℤ L}

attribute [simp] monomial_zero monomial_mul

@[ext]
theorem ext {M N : BasedChart u Λ B} (h : ∀ a, M.monomial a = N.monomial a) : M = N := by
  cases M
  cases N
  congr
  funext a
  exact h a

/-- The multiplication rule on the underlying ambient elements. -/
@[simp]
theorem val_monomial_mul (M : BasedChart u Λ B) (a b : L) :
    (M.monomial a : B) * M.monomial b =
      ((u ^ (Λ a b) : Rˣ) : R) • (M.monomial (a + b) : B) := by
  simpa only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, RingHom.coe_coe,
    Algebra.smul_def] using
    congrArg Units.val (M.monomial_mul a b)

/-- Evaluation of a based quantum torus in its chart. -/
noncomputable def eval (M : BasedChart u Λ B) : QuantumTorus R L u Λ →ₐ[R] B :=
  QuantumTorus.lift u Λ (fun a ↦ (M.monomial a : B))
    (by simp) M.val_monomial_mul

@[simp]
theorem eval_monomial (M : BasedChart u Λ B) (a : L) :
    M.eval (QuantumTorus.monomial u Λ a) = M.monomial a :=
  QuantumTorus.lift_monomial ..

/-- Chart evaluation is the linear extension along the normalized monomial basis. -/
theorem eval_toLinearMap (M : BasedChart u Λ B) :
    M.eval.toLinearMap = (QuantumTorus.basis u Λ).constr R (fun a ↦ (M.monomial a : B)) := by
  apply (QuantumTorus.basis u Λ).ext
  intro a
  rw [Module.Basis.constr_basis]
  simp

/-- A chart evaluates distinct finite Laurent combinations to distinct elements. -/
theorem eval_injective (M : BasedChart u Λ B) : Function.Injective M.eval := by
  rw [← AlgHom.coe_toLinearMap, M.eval_toLinearMap]
  exact (QuantumTorus.basis u Λ).injective_constr_of_linearIndependent M.linearIndependent

/-- Transport a chart through an injective map of ambient algebras. -/
noncomputable def map (M : BasedChart u Λ B) (f : B →ₐ[R] C) (hf : Function.Injective f) :
    BasedChart u Λ C where
  monomial a := Units.map f (M.monomial a)
  monomial_zero := by simp
  monomial_mul a b := by
    apply Units.ext
    simpa only [Units.val_mul, Units.coe_map, map_mul, map_smul, MonoidHom.coe_ofClass,
      RingHom.coe_coe, AlgHom.coe_toMonoidHom, AlgHom.commutes,
      Algebra.smul_def] using congrArg f (M.val_monomial_mul a b)
  linearIndependent := by
    simpa only [Function.comp_def, AlgHom.toLinearMap_apply, Units.coe_map,
      AlgHom.coe_toMonoidHom] using
      M.linearIndependent.map_injOn f.toLinearMap hf.injOn

@[simp]
theorem map_monomial (M : BasedChart u Λ B) (f : B →ₐ[R] C) (hf : Function.Injective f)
    (a : L) : (M.map f hf).monomial a = Units.map f (M.monomial a) :=
  (rfl)

@[simp]
theorem eval_map (M : BasedChart u Λ B) (f : B →ₐ[R] C) (hf : Function.Injective f) :
    (M.map f hf).eval = f.comp M.eval := by
  ext a
  simp

@[simp]
theorem map_id (M : BasedChart u Λ B) : M.map (AlgHom.id R B) Function.injective_id = M := by
  apply BasedChart.ext
  intro a
  apply Units.ext
  rfl

/-- Ambient transport respects composition. -/
@[simp]
theorem map_map (M : BasedChart u Λ B) (f : B →ₐ[R] C) (hf : Function.Injective f)
    (g : C →ₐ[R] D) (hg : Function.Injective g) :
    (M.map f hf).map g hg = M.map (g.comp f) (hg.comp hf) := by
  apply BasedChart.ext
  intro a
  apply Units.ext
  rfl

/-- For alternating forms, negation of an exponent inverts its monomial. -/
theorem monomial_neg (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) :
    M.monomial (-a) = (M.monomial a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simp [hΛ.self_eq_zero]

/-- Negation of an exponent inverts a monomial up to the diagonal factor. -/
theorem monomial_neg_eq_inv (M : BasedChart u Λ B) (a : L) :
    M.monomial (-a) = (Units.map (algebraMap R B) (u ^ (Λ a a)) * M.monomial a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [mul_assoc, M.monomial_mul, add_neg_cancel, M.monomial_zero, mul_one]
  rw [map_neg (Λ a) a, zpow_neg, ← map_mul, mul_inv_cancel, map_one]

/-- Alternation gives the usual quasi-commutation factor in the group of units. -/
theorem monomial_mul_monomial_eq_smul_mul (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a b : L) :
    M.monomial a * M.monomial b =
      Units.map (algebraMap R B) (u ^ (2 * Λ a b)) * (M.monomial b * M.monomial a) := by
  rw [M.monomial_mul, M.monomial_mul, ← mul_assoc, ← hΛ.neg_eq]
  simp only [← map_mul, ← zpow_add, add_comm b a]
  congr 1
  rw [show 2 * -(Λ b a) + Λ b a = -(Λ b a) by omega]

/-- Alternation gives the usual quasi-commutation factor in the ambient algebra. -/
theorem val_monomial_mul_monomial_eq_smul_mul (M : BasedChart u Λ B) (hΛ : Λ.IsAlt)
    (a b : L) : (M.monomial a : B) * M.monomial b =
      ((u ^ (2 * Λ a b) : Rˣ) : R) • ((M.monomial b : B) * M.monomial a) := by
  simpa only [Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, RingHom.coe_coe,
    Algebra.smul_def] using congrArg Units.val (M.monomial_mul_monomial_eq_smul_mul hΛ a b)

/-- The identity map gives the canonical chart of the based torus in itself. -/
noncomputable def canonical (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) :
    BasedChart u Λ (QuantumTorus R L u Λ) where
  monomial := QuantumTorus.monomialUnit u Λ
  monomial_zero := QuantumTorus.monomialUnit_zero u Λ
  monomial_mul := QuantumTorus.monomialUnit_mul u Λ
  linearIndependent := by
    have h : (fun a ↦ ((QuantumTorus.monomialUnit u Λ a) :
        QuantumTorus R L u Λ)) = (QuantumTorus.basis u Λ) := by
      funext a
      simp
    exact h.symm ▸ (QuantumTorus.basis u Λ).linearIndependent

@[simp]
theorem canonical_monomial (a : L) :
    (canonical u Λ).monomial a = QuantumTorus.monomialUnit u Λ a :=
  (rfl)

/-- An injective algebra map from the based quantum torus into an ambient algebra
gives a faithful based chart. -/
noncomputable def ofInjective (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) : BasedChart u Λ B :=
  (canonical u Λ).map f hf

@[simp]
theorem ofInjective_monomial (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) (a : L) :
    (ofInjective f hf).monomial a = Units.map f (QuantumTorus.monomialUnit u Λ a) :=
  (rfl)

@[simp]
theorem map_eval_monomialUnit (M : BasedChart u Λ B) (a : L) :
    Units.map M.eval (QuantumTorus.monomialUnit u Λ a) = M.monomial a := by
  apply Units.ext
  simp

@[simp]
theorem eval_ofInjective (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) : (ofInjective f hf).eval = f := by
  ext a
  simp

@[simp]
theorem ofInjective_eval (M : BasedChart u Λ B) : ofInjective M.eval M.eval_injective = M := by
  apply BasedChart.ext
  intro a
  simp

@[simp]
theorem eval_canonical : (canonical u Λ).eval = AlgHom.id R _ := by
  ext a
  simp

/-- Faithful monomial families are equivalent to injective maps from the based torus. -/
noncomputable def evalEquiv :
    BasedChart u Λ B ≃ {f : QuantumTorus R L u Λ →ₐ[R] B // Function.Injective f} where
  toFun M := ⟨M.eval, M.eval_injective⟩
  invFun f := ofInjective f.val f.property
  left_inv := ofInjective_eval
  right_inv f := Subtype.ext (eval_ofInjective f.val f.property)

@[simp]
theorem evalEquiv_apply (M : BasedChart u Λ B) : (evalEquiv M).val = M.eval :=
  (rfl)

@[simp]
theorem evalEquiv_symm_apply (f : {f : QuantumTorus R L u Λ →ₐ[R] B // Function.Injective f}) :
    evalEquiv.symm f = ofInjective f.val f.property :=
  (rfl)

/-- Evaluation on finitely supported coefficients is their finite linear combination
of chart monomials. -/
theorem eval_repr_symm (M : BasedChart u Λ B) (c : L →₀ R) :
    M.eval ((QuantumTorus.basis u Λ).repr.symm c) =
      c.sum (fun a r ↦ r • (M.monomial a : B)) := by
  rw [← AlgHom.toLinearMap_apply, M.eval_toLinearMap, Module.Basis.constr_apply,
    LinearEquiv.apply_symm_apply]

/-- The underlying monomial, including the diagonal correction for a non-alternating form. -/
@[simp]
theorem inv_monomial (M : BasedChart u Λ B) (a : L) :
    (((M.monomial a)⁻¹ : Bˣ) : B) =
      ((u ^ (Λ a a) : Rˣ) : R) • (M.monomial (-a) : B) := by
  have h : (M.monomial a)⁻¹ = Units.map M.eval ((QuantumTorus.monomialUnit u Λ a)⁻¹) := by
    rw [map_inv, map_eval_monomialUnit]
  rw [← Units.inv_eq_val_inv]
  change ((M.monomial a)⁻¹ : Bˣ).val = _
  rw [h]
  simp only [Units.coe_map, QuantumTorus.inv_monomialUnit, map_mul, AlgHom.coe_toMonoidHom,
    eval_monomial, AlgHom.commutes, Algebra.smul_def]

/-- For alternating forms, integer multiples of an exponent give integer powers
of its monomial. -/
theorem monomial_zsmul (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) (n : ℤ) :
    M.monomial (n • a) = M.monomial a ^ n := by
  rw [← map_eval_monomialUnit, ← QuantumTorus.monomialUnit_zpow u Λ hΛ,
    map_zpow, map_eval_monomialUnit]

/-- For alternating forms, integer powers of a chart monomial simplify to monomials. -/
@[simp]
theorem monomial_zpow (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) (n : ℤ) :
    M.monomial a ^ n = M.monomial (n • a) := by
  rw [← map_eval_monomialUnit, ← map_zpow, QuantumTorus.monomialUnit_zpow u Λ hΛ,
    map_eval_monomialUnit]

/-- For alternating forms, powers of a chart monomial simplify to monomials. -/
@[simp]
theorem monomial_pow (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) (n : ℕ) :
    M.monomial a ^ n = M.monomial (n • a) := by
  simpa using M.monomial_zpow hΛ a n

/-- For alternating forms, powers of an underlying monomial simplify to monomials. -/
@[simp]
theorem val_monomial_pow (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) (n : ℕ) :
    (M.monomial a : B) ^ n = (M.monomial (n • a) : B) := by
  simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val (M.monomial_pow hΛ a n)

/-- The coordinate units of a chart relative to a lattice basis. -/
noncomputable def coordinate {I : Type*} (M : BasedChart u Λ B)
    (b : Module.Basis I ℤ L) (i : I) : Bˣ :=
  M.monomial (b i)

/-- Coordinates are the monomials at the chosen basis vectors. -/
theorem coordinate_def {I : Type*} (M : BasedChart u Λ B) (b : Module.Basis I ℤ L) (i : I) :
    M.coordinate b i = M.monomial (b i) :=
  (rfl)

/-- Agreement on a spanning set determines every normalized monomial of a chart. -/
theorem ext_of_span_eq_top {M N : BasedChart u Λ B} (s : Set L)
    (hs : Submodule.span ℤ s = ⊤) (h : ∀ a ∈ s, M.monomial a = N.monomial a) : M = N := by
  let S : AddSubgroup L :=
    { carrier := {a | M.monomial a = N.monomial a}
      zero_mem' := by simp
      add_mem' {x y} hx hy := by
        apply mul_left_cancel (a := Units.map (algebraMap R B) (u ^ (Λ x y)))
        rw [← M.monomial_mul, ← N.monomial_mul, hx, hy]
      neg_mem' {x} hx :=
        (M.monomial_neg_eq_inv x).trans (by rw [N.monomial_neg_eq_inv, hx]) }
  apply BasedChart.ext
  intro a
  suffices a ∈ S.toIntSubmodule from this
  have ha : a ∈ Submodule.span ℤ s := by rw [hs]; trivial
  induction ha using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact S.zero_mem
  | add x y _ _ hx hy => exact S.add_mem hx hy
  | smul n x _ hx => exact S.zsmul_mem hx n

/-- Coordinate agreement determines every normalized monomial of a chart. -/
theorem ext_coordinate {I : Type*} {M N : BasedChart u Λ B}
    (b : Module.Basis I ℤ L) (h : ∀ i, M.coordinate b i = N.coordinate b i) : M = N := by
  apply ext_of_span_eq_top (Set.range b) b.span_eq
  rintro _ ⟨i, rfl⟩
  exact h i

@[simp]
theorem coordinate_ofInjective {I : Type*} (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) (b : Module.Basis I ℤ L) (i : I) :
    (ofInjective f hf).coordinate b i = Units.map f ((canonical u Λ).coordinate b i) :=
  (rfl)

@[simp]
theorem coordinate_canonical {I : Type*} (b : Module.Basis I ℤ L) (i : I) :
    (canonical u Λ).coordinate b i = QuantumTorus.monomialUnit u Λ (b i) :=
  (rfl)

/-- Ambient transport applies the ambient homomorphism to each coordinate. -/
@[simp]
theorem coordinate_map {I : Type*} (M : BasedChart u Λ B) (b : Module.Basis I ℤ L)
    (f : B →ₐ[R] C) (hf : Function.Injective f) (i : I) :
    (M.map f hf).coordinate b i = Units.map f (M.coordinate b i) :=
  (rfl)

section Reindex

variable {L' L'' : Type*} [AddCommGroup L'] [AddCommGroup L'']
  {Λ' : LinearMap.BilinForm ℤ L'} {Λ'' : LinearMap.BilinForm ℤ L''}

/-- Pull back a chart along an injective lattice map preserving its integral form. -/
noncomputable def comap (M : BasedChart u Λ B) (f : L' →ₗ[ℤ] L)
    (hf : Function.Injective f) (hfΛ : ∀ a b, Λ (f a) (f b) = Λ' a b) : BasedChart u Λ' B where
  monomial a := M.monomial (f a)
  monomial_zero := by simp
  monomial_mul a b := by simp [← hfΛ]
  linearIndependent := M.linearIndependent.comp f hf

@[simp] theorem comap_monomial (M : BasedChart u Λ B) (f : L' →ₗ[ℤ] L)
    (hf : Function.Injective f) (hfΛ : ∀ a b, Λ (f a) (f b) = Λ' a b) (a : L') :
    (M.comap f hf hfΛ).monomial a = M.monomial (f a) :=
  (rfl)

@[simp] theorem comap_id (M : BasedChart u Λ B) :
    M.comap (LinearMap.id) Function.injective_id (fun _ _ ↦ rfl) = M := by
  ext
  rfl

/-- Pulling back respects composition of lattice maps. -/
@[simp] theorem comap_comap (M : BasedChart u Λ B) (f : L' →ₗ[ℤ] L)
    (hf : Function.Injective f) (hfΛ : ∀ a b, Λ (f a) (f b) = Λ' a b)
    (g : L'' →ₗ[ℤ] L') (hg : Function.Injective g)
    (hgΛ : ∀ a b, Λ' (g a) (g b) = Λ'' a b) :
    (M.comap f hf hfΛ).comap g hg hgΛ =
      M.comap (f.comp g) (hf.comp hg) (fun a b ↦ (hfΛ (g a) (g b)).trans (hgΛ a b)) := by
  ext
  rfl

/-- Lattice pullback commutes with injective ambient transport. -/
@[simp] theorem comap_map (M : BasedChart u Λ B) (f : L' →ₗ[ℤ] L)
    (hf : Function.Injective f) (hfΛ : ∀ a b, Λ (f a) (f b) = Λ' a b)
    (g : B →ₐ[R] C) (hg : Function.Injective g) :
    (M.map g hg).comap f hf hfΛ = (M.comap f hf hfΛ).map g hg := by
  ext
  rfl

/-- Reindex a chart along a lattice isomorphism preserving its integral form. -/
noncomputable def reindex (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b) : BasedChart u Λ' B :=
  M.comap e.symm e.symm.injective (fun a b ↦ by simp [← he])

@[simp]
theorem reindex_monomial (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b) (a : L') :
    (M.reindex e he).monomial a = M.monomial (e.symm a) :=
  (rfl)

@[simp]
theorem reindex_refl (M : BasedChart u Λ B) :
    M.reindex (LinearEquiv.refl ℤ L) (fun _ _ ↦ rfl) = M := by
  apply BasedChart.ext
  intro a
  rfl

/-- Reindexing respects composition of lattice isomorphisms. -/
theorem reindex_reindex (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L') (e' : L' ≃ₗ[ℤ] L'')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b)
    (he' : ∀ a b, Λ'' (e' a) (e' b) = Λ' a b) :
    (M.reindex e he).reindex e' he' =
      M.reindex (e.trans e') (fun a b ↦ (he' (e a) (e b)).trans (he a b)) := by
  apply BasedChart.ext
  intro a
  rfl

@[simp]
theorem reindex_reindex_symm (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b)
    (he' : ∀ a b, Λ (e.symm a) (e.symm b) = Λ' a b) :
    (M.reindex e he).reindex e.symm he' = M := by
  apply BasedChart.ext
  intro a
  simp

/-- Coordinate reindexing uses the transported lattice basis. -/
@[simp]
theorem coordinate_reindex {I : Type*} (M : BasedChart u Λ B) (b : Module.Basis I ℤ L)
    (e : L ≃ₗ[ℤ] L') (he : ∀ a b, Λ' (e a) (e b) = Λ a b) (i : I) :
    (M.reindex e he).coordinate (b.map e) i = M.coordinate b i := by
  simp [coordinate_def]

/-- Lattice reindexing commutes with injective ambient transport. -/
theorem reindex_map (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b) (f : B →ₐ[R] C) (hf : Function.Injective f) :
    (M.map f hf).reindex e he = (M.reindex e he).map f hf := by
  apply BasedChart.ext
  intro a
  rfl

end Reindex

/-- When all twist factors are one, based charts are exactly injective maps from the
ordinary lattice algebra. For `L = I →₀ ℤ` this is the Laurent-chart presentation. -/
noncomputable def untwistedEquiv (h : ∀ a b, u ^ (Λ a b) = 1) :
    BasedChart u Λ B ≃ {f : AddMonoidAlgebra R L →ₐ[R] B // Function.Injective f} := by
  let e := QuantumTorus.untwistedEquiv u Λ h
  exact evalEquiv.trans ((e.arrowCongr (AlgEquiv.refl : B ≃ₐ[R] B)).subtypeEquiv
    fun f ↦ by simp [e.symm.bijective])

@[simp]
theorem untwistedEquiv_apply_single (h : ∀ a b, u ^ (Λ a b) = 1)
    (M : BasedChart u Λ B) (a : L) (r : R) :
    (untwistedEquiv h M).val (AddMonoidAlgebra.single a r) = r • (M.monomial a : B) := by
  simp [untwistedEquiv, evalEquiv]

@[simp]
theorem val_untwistedEquiv_symm_monomial (h : ∀ a b, u ^ (Λ a b) = 1)
    (f : {f : AddMonoidAlgebra R L →ₐ[R] B // Function.Injective f}) (a : L) :
    (((untwistedEquiv h).symm f).monomial a : B) = f.val (AddMonoidAlgebra.single a 1) := by
  simp [untwistedEquiv, evalEquiv]
end BasedChart

end TauCeti
