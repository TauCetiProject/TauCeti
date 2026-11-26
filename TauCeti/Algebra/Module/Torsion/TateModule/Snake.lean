/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.Algebra.Module.Torsion.TateModule
public import TauCeti.NumberTheory.Padics.PadicIntAdicCompletion

/-!
# The Tate module of the cokernel of a short exact sequence

Let `0 → M₁ → M₂ → M₃ → 0` be a short exact sequence of abelian groups. The connecting maps
`M₃[pⁿ] → M₁ ⧸ pⁿM₁` of the snake lemma (`TauCeti.torsionByδ`) are compatible with the transition
maps: multiplication by `p` on `M₃[pⁿ⁺¹] → M₃[pⁿ]` corresponds to reduction
`M₁ ⧸ pⁿ⁺¹M₁ → M₁ ⧸ pⁿM₁` (`TauCeti.tateModuleLevelδ_transition`). Passing to the inverse limit
gives a map from the `p`-adic Tate module `TauCeti.TateModule p M₃` to the `p`-adic completion of
`M₁`. If multiplication by `p` is bijective on `M₂`, every level map is bijective, and the Tate
module of `M₃` is the `p`-adic completion of `M₁` (`TauCeti.tateModuleδEquiv`), and for finitely
generated `M₁` it is `ℤ^_p ⊗ M₁`, `ℤ^_p` the `p`-adic completion of `ℤ`
(`TauCeti.tateModuleδEquivTensor`). For a lattice `M₁` in a real vector space `M₂` this computes
the Tate module of the torus `M₃`.

Both identifications are additive equivalences, with targets Mathlib's `AdicCompletion` for the
ideal `(p)` of `ℤ`. For prime `p` the map to the completion is semilinear along
`ℤ_[p] ≃ ℤ^_p` (`TauCeti.tateModuleδ_smul`), and for finitely generated `M₁` the Tate module of
`M₃` is `ℤ_[p] ⊗ M₁` as a `ℤ_[p]`-module (`TauCeti.tateModuleδPadicEquiv`).

## Main definitions

* `TauCeti.tateModuleLevelδ`: the connecting map `M₃[pⁿ] → M₁ ⧸ (p)ⁿM₁`.
* `TauCeti.tateModuleδ`: the map `T_p M₃ → lim M₁ ⧸ pⁿM₁` assembled from the level maps by
  `AdicCompletion.lift`.
* `TauCeti.tateModuleδEquiv`: `T_p M₃ ≃ lim M₁ ⧸ pⁿM₁`, the `p`-adic completion, when
  multiplication by `p` is bijective on `M₂`.
* `TauCeti.tateModuleδEquivTensor`: `T_p M₃ ≃ ℤ^_p ⊗ M₁` for finitely generated `M₁`, when
  multiplication by `p` is bijective on `M₂`.
* `TauCeti.tateModuleδPadicEquiv`: `T_p M₃ ≃ₗ[ℤ_[p]] ℤ_[p] ⊗ M₁` for prime `p` and finitely
  generated `M₁`, when multiplication by `p` is bijective on `M₂`.

## Main statements

* `TauCeti.tateModuleLevelδ_eq`: if `g y = x` and `f z = pⁿ y`, the class of `x` goes to the class
  of `z`.
* `TauCeti.tateModuleLevelδ_transition`: multiplication by `p` on torsion corresponds to reduction.
* `TauCeti.bijective_tateModuleLevelδ`: each level map is bijective when multiplication by `p` is
  bijective on `M₂`.
* `TauCeti.tateModuleδ_smul`: for prime `p`, the map to the completion sends `a • x` to
  `a • δ x`, with `a ∈ ℤ_[p]` acting on the completion through `ℤ_[p] ≃ ℤ^_p`.
-/

public noncomputable section

open Function Submodule

open scoped Pointwise TensorProduct

namespace TauCeti

section Level

variable (p : ℕ) {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  {f : M₁ →ₗ[ℤ] M₂} {g : M₂ →ₗ[ℤ] M₃} (hfg : Exact f g) (hf : Injective f) (hg : Surjective g)

/-- The connecting map `M₃[pⁿ] → M₁ ⧸ (p)ⁿM₁` of a short exact sequence `0 → M₁ → M₂ → M₃ → 0`,
with the target written as the `n`-th level of the `p`-adic completion of `M₁`. -/
def tateModuleLevelδ (n : ℕ) :
    TateModuleLevel p M₃ n →+ M₁ ⧸ (Ideal.span {(p : ℤ)} ^ n • ⊤ : Submodule ℤ M₁) :=
  -- `(p)ⁿ M₁ = pⁿ M₁`
  (Submodule.quotEquivOfEq _ _ (by
      rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
        Nat.cast_pow])).toAddMonoidHom.comp
    (torsionByδ ((p ^ n : ℕ) : ℤ) hfg hf hg).toAddMonoidHom

/-- The level map sends `g y` with `pⁿ y = f z` to the class of `z`. -/
theorem tateModuleLevelδ_eq {n : ℕ} (x : TateModuleLevel p M₃ n) {y : M₂} (hy : g y = x)
    {z : M₁} (hz : f z = ((p ^ n : ℕ) : ℤ) • y) :
    tateModuleLevelδ p hfg hf hg n x = Submodule.Quotient.mk z := by
  simp only [tateModuleLevelδ, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    torsionByδ_eq hfg hf hg x hy hz, LinearEquiv.coe_coe, Submodule.quotEquivOfEq_mk]

/-- **Compatibility with the transition maps.** Multiplication by `p` on `M₃[pⁿ⁺¹] → M₃[pⁿ]`
corresponds to reduction `M₁ ⧸ (p)ⁿ⁺¹M₁ → M₁ ⧸ (p)ⁿM₁`. -/
theorem tateModuleLevelδ_transition (n : ℕ) (x : TateModuleLevel p M₃ (n + 1)) :
    tateModuleLevelδ p hfg hf hg n (tateModuleTransition p M₃ n x) =
      factorPow (Ideal.span {(p : ℤ)}) M₁ n.le_succ (tateModuleLevelδ p hfg hf hg (n + 1) x) := by
  -- lift `x` to `y ∈ M₂`; then `g (pⁿ⁺¹ y) = pⁿ⁺¹ x = 0`, so `pⁿ⁺¹ y = f z`
  obtain ⟨y, hy⟩ := hg x
  obtain ⟨z, hz⟩ := (hfg _).1 <| by
    rw [map_zsmul, hy]
    exact (mem_torsionBy_iff _ _).1 x.property
  have hz' : f z = ((p ^ n : ℕ) : ℤ) • p • y := by
    rw [hz, pow_succ, Nat.cast_mul, mul_smul, natCast_zsmul y p]
  rw [tateModuleLevelδ_eq p hfg hf hg x hy hz,
    tateModuleLevelδ_eq p hfg hf hg _ (by simp [hy]) hz']
  simp [factorPow]

/-- When multiplication by `p` is bijective on `M₂`, each level map `M₃[pⁿ] → M₁ ⧸ (p)ⁿM₁` is
bijective. -/
theorem bijective_tateModuleLevelδ (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) (n : ℕ) :
    Bijective (tateModuleLevelδ p hfg hf hg n) := by
  have hn : Bijective fun x : M₂ ↦ ((p ^ n : ℕ) : ℤ) • x := by
    rw [Nat.cast_pow, ← smul_iterate]
    exact hp.iterate n
  -- the connecting map is the connecting isomorphism `torsionByδEquiv`
  have he : ⇑(torsionByδ ((p ^ n : ℕ) : ℤ) hfg hf hg) = torsionByδEquiv _ hfg hf hg hn :=
    funext fun x ↦ (torsionByδEquiv_apply hfg hf hg hn x).symm
  simp only [tateModuleLevelδ, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, he]
  exact (LinearEquiv.bijective _).comp (LinearEquiv.bijective _)

/-- The map from the `p`-adic Tate module of `M₃` to the `p`-adic completion of `M₁`, assembled
from the level maps. -/
def tateModuleδ : TateModule p M₃ →+ AdicCompletion (Ideal.span {(p : ℤ)}) M₁ :=
  (AdicCompletion.lift (Ideal.span {(p : ℤ)})
    (fun n ↦ ((tateModuleLevelδ p hfg hf hg n).comp (TateModule.proj n)).toIntLinearMap)
    fun {m n} hmn ↦ LinearMap.ext fun x ↦
      (Submodule.eq_factor_of_eq_factor_succ
        (fun _ _ h ↦ pow_smul_top_le _ M₁ h :
          Antitone fun n ↦ (Ideal.span {(p : ℤ)} ^ n • ⊤ : Submodule ℤ M₁))
        (fun n ↦ tateModuleLevelδ p hfg hf hg n (TateModule.proj n x))
        (fun k ↦ by rw [← TateModule.proj_succ, tateModuleLevelδ_transition])
        hmn).symm).toAddMonoidHom

/-- The `n`-th component of the image of a Tate-module point is the image of its `n`-th level. -/
@[simp]
theorem tateModuleδ_apply_val (x : TateModule p M₃) (n : ℕ) :
    (tateModuleδ p hfg hf hg x).val n = tateModuleLevelδ p hfg hf hg n (TateModule.proj n x) :=
  -- `AdicCompletion.eval_lift_apply`, through the definition by `AdicCompletion.lift`
  (rfl)

/-- When multiplication by `p` is bijective on `M₂`, the map from the Tate module of `M₃` to the
`p`-adic completion of `M₁` is bijective. -/
theorem bijective_tateModuleδ (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) :
    Bijective (tateModuleδ p hfg hf hg) := by
  have hb := bijective_tateModuleLevelδ p hfg hf hg hp
  refine ⟨fun x y hxy ↦ TateModule.ext fun n ↦ (hb n).1 ?_, fun c ↦ ?_⟩
  · simpa using congrArg (fun z : AdicCompletion _ M₁ ↦ z.val n) hxy
  · choose u hu using fun n ↦ (hb n).2 (c.val n)
    refine ⟨TateModule.mk u fun n ↦ (hb n).1 ?_, AdicCompletion.ext fun n ↦ ?_⟩
    · rw [tateModuleLevelδ_transition, hu, hu]
      exact c.property n.le_succ
    · rw [tateModuleδ_apply_val, TateModule.proj_mk, hu]

/-- **The Tate module of a cokernel.** When multiplication by `p` is bijective on `M₂`, the
`p`-adic Tate module of `M₃` is the `p`-adic completion `lim M₁ ⧸ pⁿM₁` of `M₁`: a compatible
family of torsion points `g yₙ` with `pⁿ yₙ = f zₙ` goes to the family of classes of the `zₙ`. -/
def tateModuleδEquiv (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) :
    TateModule p M₃ ≃+ AdicCompletion (Ideal.span {(p : ℤ)}) M₁ :=
  AddEquiv.ofBijective (tateModuleδ p hfg hf hg) (bijective_tateModuleδ p hfg hf hg hp)

/-- The equivalence is the map assembled from the level maps. -/
@[simp]
theorem tateModuleδEquiv_apply (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) (x : TateModule p M₃) :
    tateModuleδEquiv p hfg hf hg hp x = tateModuleδ p hfg hf hg x :=
  (rfl)

/-- The inverse equivalence sends a compatible family of classes to the Tate-module point whose
`n`-th level is sent to the `n`-th class. -/
@[simp]
theorem tateModuleLevelδ_proj_tateModuleδEquiv_symm (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x)
    (c : AdicCompletion (Ideal.span {(p : ℤ)}) M₁) (n : ℕ) :
    tateModuleLevelδ p hfg hf hg n (TateModule.proj n ((tateModuleδEquiv p hfg hf hg hp).symm c)) =
      c.val n := by
  rw [← tateModuleδ_apply_val, ← tateModuleδEquiv_apply p hfg hf hg hp, AddEquiv.apply_symm_apply]

/-- The `n`-th level of the inverse image of `c` is the torsion point that the level map sends to
the `n`-th class of `c`. -/
theorem proj_tateModuleδEquiv_symm_eq_of_tateModuleLevelδ_eq
    (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) (c : AdicCompletion (Ideal.span {(p : ℤ)}) M₁)
    {n : ℕ} {y : TateModuleLevel p M₃ n} (hy : tateModuleLevelδ p hfg hf hg n y = c.val n) :
    TateModule.proj n ((tateModuleδEquiv p hfg hf hg hp).symm c) = y :=
  (bijective_tateModuleLevelδ p hfg hf hg hp n).1 <| by
    rw [tateModuleLevelδ_proj_tateModuleδEquiv_symm, hy]

end Level

section Finite

variable (p : ℕ) {M₁ : Type} {M₂ M₃ : Type*} [AddCommGroup M₁] [Module.Finite ℤ M₁]
  [AddCommGroup M₂] [AddCommGroup M₃] {f : M₁ →ₗ[ℤ] M₂} {g : M₂ →ₗ[ℤ] M₃} (hfg : Exact f g)
  (hf : Injective f) (hg : Surjective g)

/-- **The Tate module of a cokernel as `ℤ^_p ⊗ M₁`.** For finitely generated `M₁`, when
multiplication by `p` is bijective on `M₂`, the `p`-adic Tate module of `M₃` is `ℤ^_p ⊗ M₁`, with
`ℤ^_p` the `p`-adic completion of `ℤ`, through Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
def tateModuleδEquivTensor (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) :
    TateModule p M₃ ≃+ AdicCompletion (Ideal.span {(p : ℤ)}) ℤ ⊗[ℤ] M₁ :=
  (tateModuleδEquiv p hfg hf hg hp).trans
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (Ideal.span {(p : ℤ)})
      M₁).toAddEquiv.symm

/-- Mathlib's `AdicCompletion.ofTensorProduct` turns the tensor form back into the `p`-adic
completion form of the equivalence. -/
@[simp]
theorem ofTensorProduct_tateModuleδEquivTensor (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x)
    (x : TateModule p M₃) :
    AdicCompletion.ofTensorProduct (Ideal.span {(p : ℤ)}) M₁
        (tateModuleδEquivTensor p hfg hf hg hp x) =
      tateModuleδEquiv p hfg hf hg hp x :=
  (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (Ideal.span {(p : ℤ)})
    M₁).apply_symm_apply _

end Finite

section Padic

variable (p : ℕ) [Fact p.Prime] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
  [AddCommGroup M₃] {f : M₁ →ₗ[ℤ] M₂} {g : M₂ →ₗ[ℤ] M₃} (hfg : Exact f g) (hf : Injective f)
  (hg : Surjective g)

/-- **The map to the completion is `ℤ_[p]`-semilinear.** It sends `a • x` to `a • δ x`, where
`a ∈ ℤ_[p]` acts on the `p`-adic completion of `M₁` through `ℤ_[p] ≃ ℤ^_p`
(`PadicInt.adicCompletionRingEquiv`). -/
@[simp]
theorem tateModuleδ_smul (a : ℤ_[p]) (x : TateModule p M₃) :
    tateModuleδ p hfg hf hg (a • x) =
      PadicInt.adicCompletionRingEquiv p a • tateModuleδ p hfg hf hg x := by
  refine AdicCompletion.ext fun n ↦ ?_
  simp only [tateModuleδ_apply_val, TateModule.proj_smul, AdicCompletion.smul_eval,
    AdicCompletion.val_smul_eq_evalₐ_smul, PadicInt.evalₐ_adicCompletionRingEquiv]
  generalize PadicInt.toZModPow n a = c
  rw [← ZMod.intCast_zmod_cast c, map_intCast, Int.cast_smul_eq_zsmul, map_zsmul]
  -- the integer `c.cast` acts on `M₁ ⧸ (p)ⁿM₁` through its residue in `ℤ ⧸ (p)ⁿ`
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _
    (tateModuleLevelδ p hfg hf hg n (TateModule.proj n x))
  rw [← hz, ← map_intCast (Ideal.Quotient.mk (Ideal.span {(p : ℤ)} ^ n))]
  exact AdicCompletion.mk_smul_mk _ _ _

end Padic

section PadicFinite

variable (p : ℕ) [Fact p.Prime] {M₁ : Type} {M₂ M₃ : Type*} [AddCommGroup M₁]
  [Module.Finite ℤ M₁] [AddCommGroup M₂] [AddCommGroup M₃] {f : M₁ →ₗ[ℤ] M₂} {g : M₂ →ₗ[ℤ] M₃}
  (hfg : Exact f g) (hf : Injective f) (hg : Surjective g)

/-- **The Tate module of a cokernel as `ℤ_[p] ⊗ M₁`, `ℤ_[p]`-linearly.** For prime `p` and
finitely generated `M₁`, when multiplication by `p` is bijective on `M₂`, the `p`-adic Tate module
of `M₃` is `ℤ_[p] ⊗ M₁` as a `ℤ_[p]`-module: `TauCeti.tateModuleδEquiv` followed by the inverse of
`PadicInt.tensorAdicCompletionEquiv`. -/
def tateModuleδPadicEquiv (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x) :
    TateModule p M₃ ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] M₁ :=
  ((tateModuleδEquiv p hfg hf hg hp).trans
      (PadicInt.tensorAdicCompletionEquiv p M₁).toAddEquiv.symm).toLinearEquiv
    fun a x ↦ (PadicInt.tensorAdicCompletionEquiv p M₁).injective <| by
      simp

/-- `PadicInt.tensorAdicCompletionEquiv` turns the tensor form back into the `p`-adic completion
form of the equivalence. -/
@[simp]
theorem tensorAdicCompletionEquiv_tateModuleδPadicEquiv (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x)
    (x : TateModule p M₃) :
    PadicInt.tensorAdicCompletionEquiv p M₁ (tateModuleδPadicEquiv p hfg hf hg hp x) =
      tateModuleδEquiv p hfg hf hg hp x :=
  (PadicInt.tensorAdicCompletionEquiv p M₁).apply_symm_apply _

/-- The inverse equivalence is `PadicInt.tensorAdicCompletionEquiv` followed by the inverse of
`TauCeti.tateModuleδEquiv`. -/
theorem tateModuleδPadicEquiv_symm_apply (hp : Bijective fun x : M₂ ↦ (p : ℤ) • x)
    (t : ℤ_[p] ⊗[ℤ] M₁) :
    (tateModuleδPadicEquiv p hfg hf hg hp).symm t =
      (tateModuleδEquiv p hfg hf hg hp).symm (PadicInt.tensorAdicCompletionEquiv p M₁ t) := by
  rw [LinearEquiv.symm_apply_eq]
  apply (PadicInt.tensorAdicCompletionEquiv p M₁).injective
  simp

end PadicFinite

end TauCeti
