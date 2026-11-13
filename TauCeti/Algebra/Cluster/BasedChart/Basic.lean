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

`BasedChart.eval` extends the monomial family to an injective algebra map from the
based quantum torus. Conversely, an injective algebra map gives such a chart.
`BasedChart.evalEquiv` identifies these two presentations when the integral form is
alternating. `BasedChart.map` transports charts along injective ambient algebra maps,
and `BasedChart.reindex` transports them along isomorphisms of exponent lattices.
Coordinates in any lattice basis determine an alternating chart, and
`BasedChart.zeroFormEquiv` recovers ordinary Laurent charts for the zero form.

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
theorem map_comp (M : BasedChart u Λ B) (f : B →ₐ[R] C) (hf : Function.Injective f)
    (g : C →ₐ[R] D) (hg : Function.Injective g) :
    (M.map f hf).map g hg = M.map (g.comp f) (hg.comp hf) := by
  apply BasedChart.ext
  intro a
  apply Units.ext
  rfl

/-- For alternating forms, negation of an exponent inverts its monomial. -/
@[simp]
theorem monomial_neg (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) :
    M.monomial (-a) = (M.monomial a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  simp [hΛ.self_eq_zero]

/-- An injective map of based quantum tori gives a faithful based chart. -/
noncomputable def ofInjective (hΛ : Λ.IsAlt) (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) : BasedChart u Λ B where
  monomial a := Units.map f (QuantumTorus.monomialUnit u Λ hΛ a)
  monomial_zero := by simp
  monomial_mul a b := by
    apply Units.ext
    simpa only [Units.val_mul, Units.coe_map, QuantumTorus.val_monomialUnit,
      MonoidHom.coe_ofClass, RingHom.coe_coe, AlgHom.coe_toMonoidHom,
      map_mul, map_smul, AlgHom.commutes, Algebra.smul_def] using
      congrArg f (QuantumTorus.monomial_mul_monomial u Λ a b)
  linearIndependent := by
    simpa only [Function.comp_def, AlgHom.toLinearMap_apply, QuantumTorus.basis_apply,
      Units.coe_map, AlgHom.coe_toMonoidHom, QuantumTorus.val_monomialUnit] using
      (QuantumTorus.basis u Λ).linearIndependent.map_injOn f.toLinearMap hf.injOn

@[simp]
theorem ofInjective_monomial (hΛ : Λ.IsAlt) (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) (a : L) :
    (ofInjective hΛ f hf).monomial a = Units.map f (QuantumTorus.monomialUnit u Λ hΛ a) :=
  (rfl)

@[simp]
theorem eval_ofInjective (hΛ : Λ.IsAlt) (f : QuantumTorus R L u Λ →ₐ[R] B)
    (hf : Function.Injective f) : (ofInjective hΛ f hf).eval = f := by
  ext a
  simp

@[simp]
theorem ofInjective_eval (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) :
    ofInjective hΛ M.eval M.eval_injective = M := by
  apply BasedChart.ext
  intro a
  apply Units.ext
  simp

/-- Faithful monomial families are equivalent to injective maps from the based torus. -/
noncomputable def evalEquiv (hΛ : Λ.IsAlt) :
    BasedChart u Λ B ≃ {f : QuantumTorus R L u Λ →ₐ[R] B // Function.Injective f} where
  toFun M := ⟨M.eval, M.eval_injective⟩
  invFun f := ofInjective hΛ f.val f.property
  left_inv M := M.ofInjective_eval hΛ
  right_inv f := Subtype.ext (eval_ofInjective hΛ f.val f.property)

@[simp]
theorem evalEquiv_apply (hΛ : Λ.IsAlt) (M : BasedChart u Λ B) :
    (evalEquiv hΛ M).val = M.eval :=
  (rfl)

@[simp]
theorem evalEquiv_symm_apply (hΛ : Λ.IsAlt)
    (f : {f : QuantumTorus R L u Λ →ₐ[R] B // Function.Injective f}) :
    (evalEquiv hΛ).symm f = ofInjective hΛ f.val f.property :=
  (rfl)

/-- The identity map gives the canonical chart of the based torus in itself. -/
noncomputable def canonical (u : Rˣ) (Λ : LinearMap.BilinForm ℤ L) (hΛ : Λ.IsAlt) :
    BasedChart u Λ (QuantumTorus R L u Λ) :=
  ofInjective hΛ (AlgHom.id R _) Function.injective_id

@[simp]
theorem canonical_monomial (hΛ : Λ.IsAlt) (a : L) :
    (canonical u Λ hΛ).monomial a = QuantumTorus.monomialUnit u Λ hΛ a := by
  apply Units.ext
  rfl

@[simp]
theorem eval_canonical (hΛ : Λ.IsAlt) :
    (canonical u Λ hΛ).eval = AlgHom.id R _ :=
  eval_ofInjective hΛ _ _

/-- Evaluation on finitely supported coefficients is their finite linear combination
of chart monomials. -/
theorem eval_repr_symm (M : BasedChart u Λ B) (c : L →₀ R) :
    M.eval ((QuantumTorus.basis u Λ).repr.symm c) =
      c.sum (fun a r ↦ r • (M.monomial a : B)) := by
  rw [← AlgHom.toLinearMap_apply, M.eval_toLinearMap, Module.Basis.constr_apply,
    LinearEquiv.apply_symm_apply]

/-- Integer multiples of a single exponent give integer powers of its monomial. -/
@[simp]
theorem monomial_zsmul (M : BasedChart u Λ B) (hΛ : Λ.IsAlt) (a : L) (n : ℤ) :
    M.monomial (n • a) = M.monomial a ^ n := by
  let f : Multiplicative ℤ →* Bˣ :=
    { toFun := fun m ↦ M.monomial (m.toAdd • a)
      map_one' := by simp
      map_mul' := fun m n ↦ by
        simp [add_zsmul, M.monomial_mul, hΛ.self_eq_zero] }
  simpa [f] using f.map_zpow (Multiplicative.ofAdd (1 : ℤ)) n

/-- The coordinate units of a chart relative to a lattice basis. -/
noncomputable def coordinate {I : Type*} (M : BasedChart u Λ B)
    (b : Module.Basis I ℤ L) (i : I) : Bˣ :=
  M.monomial (b i)

/-- Coordinates are the monomials at the chosen basis vectors. -/
theorem coordinate_def {I : Type*} (M : BasedChart u Λ B) (b : Module.Basis I ℤ L) (i : I) :
    M.coordinate b i = M.monomial (b i) :=
  (rfl)

/-- Coordinate agreement determines every normalized monomial of an alternating chart. -/
theorem ext_coordinate {I : Type*} {M N : BasedChart u Λ B} (hΛ : Λ.IsAlt)
    (b : Module.Basis I ℤ L) (h : ∀ i, M.coordinate b i = N.coordinate b i) : M = N := by
  apply BasedChart.ext
  intro a
  have ha : a ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact h i
  | zero => simp
  | add x y _ _ hx hy =>
    apply mul_left_cancel (a := Units.map (algebraMap R B) (u ^ (Λ x y)))
    rw [← M.monomial_mul, ← N.monomial_mul, hx, hy]
  | smul n x _ hx => simp [M.monomial_zsmul hΛ, N.monomial_zsmul hΛ, hx]

/-- Ambient transport applies the ambient homomorphism to each coordinate. -/
@[simp]
theorem coordinate_map {I : Type*} (M : BasedChart u Λ B) (b : Module.Basis I ℤ L)
    (f : B →ₐ[R] C) (hf : Function.Injective f) (i : I) :
    (M.map f hf).coordinate b i = Units.map f (M.coordinate b i) :=
  (rfl)

section Reindex

variable {L' L'' : Type*} [AddCommGroup L'] [AddCommGroup L'']
  {Λ' : LinearMap.BilinForm ℤ L'} {Λ'' : LinearMap.BilinForm ℤ L''}

/-- Reindex a chart along a lattice isomorphism preserving its integral form. -/
noncomputable def reindex (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b) : BasedChart u Λ' B where
  monomial a := M.monomial (e.symm a)
  monomial_zero := by simp
  monomial_mul a b := by
    rw [M.monomial_mul, map_add]
    rw [← he, e.apply_symm_apply, e.apply_symm_apply]
  linearIndependent := M.linearIndependent.comp e.symm e.symm.injective

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
theorem reindex_trans (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L') (e' : L' ≃ₗ[ℤ] L'')
    (he : ∀ a b, Λ' (e a) (e b) = Λ a b)
    (he' : ∀ a b, Λ'' (e' a) (e' b) = Λ' a b) :
    (M.reindex e he).reindex e' he' =
      M.reindex (e.trans e') (fun a b ↦ (he' (e a) (e b)).trans (he a b)) := by
  apply BasedChart.ext
  intro a
  rfl

@[simp]
theorem reindex_symm (M : BasedChart u Λ B) (e : L ≃ₗ[ℤ] L')
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

/-- Zero-form based charts are exactly injective maps from the ordinary lattice
algebra. For `L = I →₀ ℤ` this is the Laurent-chart presentation. -/
noncomputable def zeroFormEquiv :
    BasedChart u (0 : LinearMap.BilinForm ℤ L) B ≃
      {f : AddMonoidAlgebra R L →ₐ[R] B // Function.Injective f} := by
  let e := QuantumTorus.untwistedEquiv u (0 : LinearMap.BilinForm ℤ L) (by simp)
  refine (evalEquiv (LinearMap.BilinForm.isAlt_zero)).trans
    { toFun := fun f ↦ ⟨f.val.comp e.symm.toAlgHom, f.property.comp e.symm.injective⟩
      invFun := fun f ↦ ⟨f.val.comp e.toAlgHom, f.property.comp e.injective⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    ext a
    simp
  · intro f
    apply Subtype.ext
    ext a
    simp

@[simp]
theorem zeroFormEquiv_apply_single (M : BasedChart u (0 : LinearMap.BilinForm ℤ L) B)
    (a : L) : (zeroFormEquiv M).val (AddMonoidAlgebra.single a 1) = M.monomial a := by
  simp [zeroFormEquiv, evalEquiv]

@[simp]
theorem zeroFormEquiv_symm_monomial
    (f : {f : AddMonoidAlgebra R L →ₐ[R] B // Function.Injective f}) (a : L) :
    (((zeroFormEquiv (u := u)).symm f).monomial a : B) =
      f.val (AddMonoidAlgebra.single a 1) := by
  simp [zeroFormEquiv, evalEquiv]

end BasedChart

end TauCeti
