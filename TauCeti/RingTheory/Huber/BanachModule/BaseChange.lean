/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.RingTheory.Huber.BanachModule.SplitExact

/-!
# Symmetry and scalar extension for completed tensor products

For a commutative topological ring `A` and topological `A`-modules `V`, `W`, this file equips
`V ⊗̂_A W` (`TauCeti.Huber.BanachModule.CompletedTensor A V W`) with:

* symmetry `V ⊗̂_A W ≃L[A] W ⊗̂_A V` (`comm`), congruence (`congr`), and right unit
  `M ⊗̂_A A ≃L[A] M` (`rid`);
* functorial `S`-linear scalar extension `f ↦ 1_S ⊗̂ f : S ⊗̂_A M →L[S] S ⊗̂_A N` along a
  commutative topological `A`-algebra `S` (`baseChange`, `baseChangeCongr`), preserving ring
  operations, polynomial evaluation, retracts, and continuously split exact sequences
  (`exact_baseChange_of_split`);
* the algebraic-to-completed isomorphism `S ⊗[A] P ≃ₗ[S] S ⊗̂_A P` for a finite projective
  `A`-module `P` (`finiteProjectiveBaseChangeEquiv`).

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: Foundations*, Astérisque 371 (2015),
  §2.1–2.2.
-/

public section

open Function TensorProduct Topology

namespace TauCeti.Huber.BanachModule.CompletedTensor

local notation:max V " ⊗̂[" A "] " W => CompletedTensor A V W

section CommAndUnit

variable (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (V : Type*) [AddCommGroup V] [Module A V] [TopologicalSpace V]
  (W : Type*) [AddCommGroup W] [Module A W] [TopologicalSpace W]

/-- The continuous `A`-linear swap map `V ⊗̂_A W →L[A] W ⊗̂_A V`. -/
private noncomputable def commHom : (V ⊗̂[A] W) →L[A] (W ⊗̂[A] V) :=
  lift (tmul A W V).flip (((continuous_tmul A W V).comp continuous_swap).congr fun _ ↦ rfl)

private theorem commHom_tmul (v : V) (w : W) :
    commHom A V W (tmul A V W v w) = tmul A W V w v := by simp [commHom]

/-- **Symmetry of the completed tensor product**: `V ⊗̂_A W ≃L[A] W ⊗̂_A V`, sending `v ⊗ w` to
`w ⊗ v` (`comm_tmul`). -/
noncomputable def comm : (V ⊗̂[A] W) ≃L[A] (W ⊗̂[A] V) :=
  .ofContinuousLinearMap (commHom A V W) (commHom A W V)
    (ext fun _ _ ↦ by simp [commHom_tmul]) (ext fun _ _ ↦ by simp [commHom_tmul])

variable {A V W}

/-- `comm` swaps the factors of an elementary tensor. -/
@[simp]
theorem comm_tmul (v : V) (w : W) : comm A V W (tmul A V W v w) = tmul A W V w v :=
  commHom_tmul A V W v w

/-- `comm` extends `TensorProduct.comm` from the algebraic tensor product. -/
@[simp]
theorem comm_toCompletion (x : V ⊗[A] W) :
    comm A V W (toCompletion A V W x) = toCompletion A W V (TensorProduct.comm A V W x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The inverse of `comm` is `comm` with the factors swapped. -/
@[simp]
theorem comm_symm : (comm A V W).symm = comm A W V := (rfl)

/-- Applying `comm` twice is the identity. -/
@[simp]
theorem comm_comm (z : V ⊗̂[A] W) : comm A W V (comm A V W z) = z := (comm A V W).symm_apply_apply z

section Congr

variable {V' : Type*} [AddCommGroup V'] [Module A V'] [TopologicalSpace V']
  {W' : Type*} [AddCommGroup W'] [Module A W'] [TopologicalSpace W']

/-- `comm` intertwines `map f g` with `map g f`. -/
theorem comm_map (f : V →L[A] V') (g : W →L[A] W') :
    (comm A V' W' : (V' ⊗̂[A] W') →L[A] (W' ⊗̂[A] V')).comp (map f g) =
      (map g f).comp (comm A V W : (V ⊗̂[A] W) →L[A] (W ⊗̂[A] V)) := ext fun _ _ ↦ by simp

/-- Applying `comm` after `map f g` equals applying `map g f` after `comm`. -/
theorem comm_map_apply (f : V →L[A] V') (g : W →L[A] W') (z : V ⊗̂[A] W) :
    comm A V' W' (map f g z) = map g f (comm A V W z) := DFunLike.congr_fun (comm_map f g) z

/-- **Congruence of completed tensor products** along continuous linear equivalences of the
factors. -/
noncomputable def congr (eV : V ≃L[A] V') (eW : W ≃L[A] W') : (V ⊗̂[A] W) ≃L[A] (V' ⊗̂[A] W') :=
  .ofContinuousLinearMap (map (eV : V →L[A] V') (eW : W →L[A] W'))
    (map (eV.symm : V' →L[A] V) (eW.symm : W' →L[A] W))
    (ext fun _ _ ↦ by simp) (ext fun _ _ ↦ by simp)

/-- `congr eV eW` is `map eV eW`. -/
theorem congr_apply (eV : V ≃L[A] V') (eW : W ≃L[A] W') (z : V ⊗̂[A] W) :
    congr eV eW z = map (eV : V →L[A] V') (eW : W →L[A] W') z := (rfl)

/-- `congr eV eW` sends `v ⊗ w` to `eV v ⊗ eW w`. -/
@[simp]
theorem congr_tmul (eV : V ≃L[A] V') (eW : W ≃L[A] W') (v : V) (w : W) :
    congr eV eW (tmul A V W v w) = tmul A V' W' (eV v) (eW w) := by simp [congr_apply]

/-- The inverse of `congr eV eW` is `congr eV.symm eW.symm`. -/
@[simp]
theorem congr_symm (eV : V ≃L[A] V') (eW : W ≃L[A] W') :
    (congr eV eW).symm = congr eV.symm eW.symm := (rfl)

end Congr

section Rid

variable (A)
  (M : Type*) [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
  [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M] [T0Space M]

/-- **The right unit isomorphism** `M ⊗̂_A A ≃L[A] M` of a complete Hausdorff nonarchimedean
topological `A`-module `M` with continuous action: it sends `m ⊗ a` to `a • m` (`rid_tmul`), and
its inverse sends `m` to `m ⊗ 1` (`rid_symm_apply`). -/
noncomputable def rid : (M ⊗̂[A] A) ≃L[A] M := (comm A M A).trans (lid A M)

/-- The right unit isomorphism is `comm` followed by `lid`. -/
theorem rid_eq_comm_trans_lid : rid A M = (comm A M A).trans (lid A M) := (rfl)

/-- The right unit isomorphism sends `m ⊗ a` to `a • m`. -/
@[simp]
theorem rid_tmul (m : M) (a : A) : rid A M (tmul A M A m a) = a • m := by simp [rid]

/-- The inverse of the right unit isomorphism sends `m` to `m ⊗ 1`. -/
@[simp]
theorem rid_symm_apply (m : M) : (rid A M).symm m = tmul A M A m 1 := by simp [rid]

/-- The right unit isomorphism extends Mathlib's algebraic right unit map `M ⊗[A] A ≃ M`. -/
@[simp]
theorem rid_toCompletion (x : M ⊗[A] A) :
    rid A M (toCompletion A M A x) = TensorProduct.rid A M x := by
  induction x using TensorProduct.inductionOn with
  | tmul m a => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Rid

end CommAndUnit

section BaseChange

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (S : Type*) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [Algebra A S]
  {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
  {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]
  {P : Type*} [AddCommGroup P] [Module A P] [TopologicalSpace P]

omit [IsTopologicalRing A] in
/-- Two continuous `S`-linear maps out of `S ⊗̂_A M` into a Hausdorff `S`-module agree as soon as
they agree on all unit elementary tensors `1 ⊗ m`. -/
theorem ext_baseChange {E : Type*} [AddCommGroup E] [Module S E] [TopologicalSpace E] [T2Space E]
    {f g : (S ⊗̂[A] M) →L[S] E} (h : ∀ m, f (tmul A S M 1 m) = g (tmul A S M 1 m)) : f = g :=
  ext_left fun s m ↦ by
    have hs : tmul A S M s m = s • tmul A S M 1 m := by simp
    rw [hs, f.map_smul, g.map_smul, h m]

/-- **Completed scalar extension of continuous linear maps.** Along a commutative topological
`A`-algebra `S`, a continuous `A`-linear map `f : M →L[A] N` extends to the continuous `S`-linear
map `1_S ⊗̂ f : S ⊗̂_A M →L[S] S ⊗̂_A N` sending `s ⊗ m` to `s ⊗ f m` (`baseChange_tmul`). -/
noncomputable def baseChange (f : M →L[A] N) : (S ⊗̂[A] M) →L[S] (S ⊗̂[A] N) where
  toFun := map (.id A S) f
  map_add' := map_add (map (.id A S) f)
  map_smul' s z := by
    refine (denseRange_toCompletion A S M).induction_on z
      (isClosed_eq ((map (.id A S) f).continuous.comp (continuous_const_smul s))
        ((continuous_const_smul s).comp (map (.id A S) f).continuous)) fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | tmul t m => simp
    | add x y hx hy => simp only [map_add, smul_add, RingHom.id_apply] at hx hy ⊢; rw [hx, hy]
  cont := (map (.id A S) f).continuous

/-- Applying `baseChange S f` coincides with applying `map (.id A S) f`. -/
theorem baseChange_apply (f : M →L[A] N) (z : S ⊗̂[A] M) :
    baseChange S f z = map (.id A S) f z := (rfl)

/-- `baseChange S f` sends `s ⊗ m` to `s ⊗ f m`. -/
@[simp]
theorem baseChange_tmul (f : M →L[A] N) (s : S) (m : M) :
    baseChange S f (tmul A S M s m) = tmul A S N s (f m) := by simp [baseChange_apply]

/-- Completed scalar extension preserves the identity map. -/
@[simp]
theorem baseChange_id : baseChange S (.id A M) = ContinuousLinearMap.id S (S ⊗̂[A] M) :=
  ext_baseChange S fun _ ↦ by simp

/-- Completed scalar extension preserves composition. -/
theorem baseChange_comp (g : N →L[A] P) (f : M →L[A] N) :
    baseChange S (g.comp f) = (baseChange S g).comp (baseChange S f) :=
  ext_baseChange S fun _ ↦ by simp

/-- Completed scalar extension sends `0` to `0`. -/
@[simp]
theorem baseChange_zero : baseChange S (0 : M →L[A] N) = 0 := ext_baseChange S fun _ ↦ by simp

/-- Completed scalar extension is additive. -/
@[simp]
theorem baseChange_add [ContinuousAdd N] (f g : M →L[A] N) :
    baseChange S (f + g) = baseChange S f + baseChange S g := ext_baseChange S fun _ ↦ by simp

/-- Completed scalar extension commutes with negation. -/
@[simp]
theorem baseChange_neg [IsTopologicalAddGroup N] (f : M →L[A] N) :
    baseChange S (-f) = -baseChange S f := ext_baseChange S fun _ ↦ by simp

/-- Completed scalar extension commutes with subtraction. -/
@[simp]
theorem baseChange_sub [IsTopologicalAddGroup N] (f g : M →L[A] N) :
    baseChange S (f - g) = baseChange S f - baseChange S g := ext_baseChange S fun _ ↦ by simp

/-- Completed scalar extension is `A`-semilinear along `algebraMap A S`. -/
@[simp]
theorem baseChange_smul [ContinuousConstSMul A N] (a : A) (f : M →L[A] N) :
    baseChange S (a • f) = algebraMap A S a • baseChange S f :=
  ext_baseChange S fun m ↦ by
    rw [smul_apply, baseChange_tmul, smul_apply, baseChange_tmul, smul_tmul',
      algebraMap_smul, ← toCompletion_tmul, ← toCompletion_tmul, TensorProduct.smul_tmul]

/-- Completed scalar extension preserves `1` in the endomorphism ring. -/
@[simp]
theorem baseChange_one : baseChange S (1 : M →L[A] M) = 1 := baseChange_id S

/-- Completed scalar extension preserves multiplication in the endomorphism ring. -/
theorem baseChange_mul (f g : M →L[A] M) :
    baseChange S (f * g) = baseChange S f * baseChange S g := baseChange_comp S f g

/-- Completed scalar extension preserves powers in the endomorphism ring. -/
@[simp]
theorem baseChange_pow (f : M →L[A] M) (n : ℕ) : baseChange S (f ^ n) = baseChange S f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, baseChange_mul, ih]

/-- Completed scalar extension intertwines polynomial evaluation along `algebraMap A S`. -/
theorem aeval_baseChange [IsTopologicalAddGroup M] [ContinuousConstSMul A M]
    (f : M →L[A] M) (p : Polynomial A) :
    Polynomial.aeval (baseChange S f) (Polynomial.map (algebraMap A S) p) =
      baseChange S (Polynomial.aeval f p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add, map_add, map_add, baseChange_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.map_monomial, Polynomial.aeval_monomial, ← Algebra.smul_def,
      baseChange_smul, baseChange_pow]

/-- **Completed scalar extension of continuous linear equivalences**: `e : M ≃L[A] N` induces
`S ⊗̂_A M ≃L[S] S ⊗̂_A N`. -/
noncomputable def baseChangeCongr (e : M ≃L[A] N) : (S ⊗̂[A] M) ≃L[S] (S ⊗̂[A] N) :=
  .ofContinuousLinearMap (baseChange S (e : M →L[A] N)) (baseChange S (e.symm : N →L[A] M))
    (by rw [← baseChange_comp, e.coe_comp_coe_symm, baseChange_id])
    (by rw [← baseChange_comp, e.coe_symm_comp_coe, baseChange_id])

/-- `baseChangeCongr S e` acts as `baseChange S e`. -/
@[simp]
theorem baseChangeCongr_apply (e : M ≃L[A] N) (z : S ⊗̂[A] M) :
    baseChangeCongr S e z = baseChange S (e : M →L[A] N) z := (rfl)

/-- The inverse of `baseChangeCongr S e` is `baseChangeCongr S e.symm`. -/
@[simp]
theorem baseChangeCongr_symm (e : M ≃L[A] N) :
    (baseChangeCongr S e).symm = baseChangeCongr S e.symm := (rfl)

/-- **Identity base change.** Along `S = A`, the unit equivalences `lid A M` and `lid A N`
intertwine `baseChange A f` with `f`. -/
theorem lid_baseChange_apply
    {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
    [NonarchimedeanAddGroup M] [ContinuousSMul A M] [CompleteSpace M] [T0Space M]
    {N : Type*} [AddCommGroup N] [Module A N] [UniformSpace N] [IsUniformAddGroup N]
    [NonarchimedeanAddGroup N] [ContinuousSMul A N] [CompleteSpace N] [T0Space N]
    (f : M →L[A] N) (z : A ⊗̂[A] M) : lid A N (baseChange A f z) = f (lid A M z) := by
  refine (denseRange_toCompletion A A M).induction_on z
    (isClosed_eq ((lid A N).continuous.comp (baseChange A f).continuous)
      (f.continuous.comp (lid A M).continuous)) fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul _ _ => simp
  | add _ _ hx hy => simp only [map_add, hx, hy]

/-- Completed scalar extension preserves continuous linear retracts. -/
theorem baseChange_comp_eq_id_of_retract {i : M →L[A] N} {r : N →L[A] M}
    (hri : r.comp i = .id A M) : (baseChange S r).comp (baseChange S i) = .id S (S ⊗̂[A] M) := by
  rw [← baseChange_comp, hri, baseChange_id]

/-- **Split exactness of completed scalar extension.** If `i : U →L[A] V` and `p : V →L[A] Q`
satisfy `p ∘ i = 0` and admit continuous linear splitting maps `r`, `s` with `i ∘ r + s ∘ p = id`,
then `(baseChange S i, baseChange S p)` is exact. -/
theorem exact_baseChange_of_split
    {U : Type*} [AddCommGroup U] [Module A U] [TopologicalSpace U]
    {V : Type*} [AddCommGroup V] [Module A V] [TopologicalSpace V]
    {Q : Type*} [AddCommGroup Q] [Module A Q] [TopologicalSpace Q]
    {i : U →L[A] V} {p : V →L[A] Q} (r : V →L[A] U) (s : Q →L[A] V)
    (hpi : p.comp i = 0) (hsplit : ∀ v, i (r v) + s (p v) = v) :
    Exact (baseChange S i) (baseChange S p) := by
  have hex := exact_of_split (W := S) r s hpi hsplit
  have hi z : baseChange S i z = comm A V S (map i (.id A S) (comm A S U z)) := by
    rw [baseChange_apply, ← comm_map_apply (.id A S) i z, comm_comm]
  have hp z : baseChange S p z = comm A Q S (map p (.id A S) (comm A S V z)) := by
    rw [baseChange_apply, ← comm_map_apply (.id A S) p z, comm_comm]
  refine fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := (hex _).mp ((comm A Q S).injective (by simpa [hp] using hy))
    exact ⟨comm A U S x, by rw [hi, comm_comm, hx, comm_comm]⟩
  · rintro ⟨x, rfl⟩; rw [hp, hi, comm_comm, (hex _).mpr ⟨comm A S U x, rfl⟩, map_zero]

section FiniteProjective

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (S : Type*) [CommRing S] [UniformSpace S] [IsTopologicalRing S] [IsUniformAddGroup S]
  [NonarchimedeanAddGroup S] [Algebra A S] [ContinuousSMul A S] [CompleteSpace S] [T0Space S]
  (P : Type*) [AddCommGroup P] [Module A P] [TopologicalSpace P]
  [IsModuleTopology A P] [Module.Finite A P] [Module.Projective A P]

omit [IsTopologicalRing S] in
variable (A) in
/-- For a finite projective `A`-module `P` with its module topology and a complete Hausdorff
nonarchimedean topological `A`-algebra `S` with continuous `A`-action, the map
`S ⊗[A] P → S ⊗̂_A P` is bijective. -/
theorem toCompletion_bijective_of_finite_projective_right :
    Function.Bijective (toCompletion A S P) := by
  have hcomm : (toCompletion A S P : S ⊗[A] P → S ⊗̂[A] P) =
      (comm A P S) ∘ (toCompletion A P S) ∘ (TensorProduct.comm A S P) := by
    ext x; simp [Function.comp_apply]
  rw [hcomm]
  exact (comm A P S).bijective.comp
    ((toCompletion_bijective_of_finite_projective A P S).comp (TensorProduct.comm A S P).bijective)

omit [IsTopologicalRing S] in
variable (A) in
/-- **Completed scalar extension of a finite projective module**: for a finite projective
`A`-module `P` with its module topology, `S ⊗[A] P ≃ₗ[S] S ⊗̂_A P`. -/
noncomputable def finiteProjectiveBaseChangeEquiv : S ⊗[A] P ≃ₗ[S] (S ⊗̂[A] P) :=
  LinearEquiv.ofBijective
    { toFun := toCompletion A S P, map_add' := map_add _, map_smul' := toCompletion_smul }
    (toCompletion_bijective_of_finite_projective_right A S P)

/-- `finiteProjectiveBaseChangeEquiv` sends `s ⊗ₜ p` to `tmul A S P s p`. -/
@[simp]
theorem finiteProjectiveBaseChangeEquiv_tmul (s : S) (p : P) :
    finiteProjectiveBaseChangeEquiv A S P (s ⊗ₜ[A] p) = tmul A S P s p := toCompletion_tmul ..

/-- The inverse of `finiteProjectiveBaseChangeEquiv` sends `tmul A S P s p` to `s ⊗ₜ p`. -/
@[simp]
theorem finiteProjectiveBaseChangeEquiv_symm_tmul (s : S) (p : P) :
    (finiteProjectiveBaseChangeEquiv A S P).symm (tmul A S P s p) = s ⊗ₜ[A] p :=
  (finiteProjectiveBaseChangeEquiv A S P).symm_apply_eq.mpr
    (finiteProjectiveBaseChangeEquiv_tmul S P s p).symm

end FiniteProjective

end BaseChange

end TauCeti.Huber.BanachModule.CompletedTensor
