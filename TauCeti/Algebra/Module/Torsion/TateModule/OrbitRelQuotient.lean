/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.Algebra.Module.Torsion.TateModule

/-!
# The Tate module of a torus

Let `f : Λ → E` be an injective additive map and `T = E / f(Λ)` the orbit space of translation by
its range, for instance a lattice `Λ` in a real vector space `E` and its torus. If multiplication by
`p` is bijective on `E`, the connecting isomorphisms `T[pⁿ] ≃ Λ ⧸ pⁿΛ` of the sequences
`0 → Λ → E → T → 0` (`TauCeti.torsionByδ`) are compatible with the transition maps: multiplication
by `p` on `T[pⁿ⁺¹] → T[pⁿ]` corresponds to reduction `Λ ⧸ pⁿ⁺¹Λ → Λ ⧸ pⁿΛ`
(`LinearMap.orbitRelQuotientTateLevel_transition`). Passing to the inverse limit identifies the
`p`-adic Tate module `TauCeti.TateModule p T` with the `p`-adic completion of `Λ`
(`LinearMap.tateModuleOrbitRelQuotientEquiv`), and for finitely generated `Λ` with
`ℤ^_p ⊗ Λ`, `ℤ^_p` the `p`-adic completion of `ℤ`
(`LinearMap.tateModuleOrbitRelQuotientEquivTensor`).

This is the lattice side of `AbelianLattice.tate` in AbelianSchemesAndArithmeticModuli §A5.1:
for `V / Λ ≅ A^an` it gives `T_ℓ(V / Λ) ≅ Λ ⊗ ℤ_ℓ`.

## Main definitions

* `LinearMap.orbitRelQuotientTateLevel`: the connecting map `T[pⁿ] → Λ ⧸ (p)ⁿΛ`.
* `LinearMap.tateModuleOrbitRelQuotientEquiv`: `T_p T ≃ lim Λ ⧸ pⁿΛ`, the `p`-adic completion.
* `LinearMap.tateModuleOrbitRelQuotientEquivTensor`: `T_p T ≃ ℤ^_p ⊗ Λ` for finitely generated
  `Λ`.

## Main statements

* `LinearMap.orbitRelQuotientTateLevel_eq`: the class of `β` with `pⁿ β = f l` goes to the class
  of `l`.
* `LinearMap.orbitRelQuotientTateLevel_transition`: multiplication by `p` on torsion corresponds
  to reduction of lattice classes.
* `LinearMap.bijective_orbitRelQuotientTateLevel`: each level map is bijective.
-/

public noncomputable section

open Function Submodule TauCeti

open scoped Pointwise TensorProduct

namespace LinearMap

variable {Λ E : Type*} [AddCommGroup Λ] [AddCommGroup E] (f : Λ →ₗ[ℤ] E) (hf : Injective f)
  (p : ℕ)

/-- `(p)ⁿ Λ = pⁿ Λ` as submodules of `Λ`. -/
theorem span_singleton_pow_smul_top_eq (n : ℕ) :
    (Ideal.span {(p : ℤ)} ^ n • ⊤ : Submodule ℤ Λ) = ((p ^ n : ℕ) : ℤ) • (⊤ : Submodule ℤ Λ) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Nat.cast_pow]

/-- The connecting map `T[pⁿ] → Λ ⧸ (p)ⁿΛ` of the orbit space `T = E / f(Λ)`, with the target
written as the `n`-th level of the `p`-adic completion of `Λ`. -/
def orbitRelQuotientTateLevel (n : ℕ) :
    TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) n →+
      Λ ⧸ (Ideal.span {(p : ℤ)} ^ n • ⊤ : Submodule ℤ Λ) :=
  (Submodule.quotEquivOfEq _ _ (span_singleton_pow_smul_top_eq p n).symm).toAddMonoidHom.comp
    (f.orbitRelQuotientTorsionByδ hf ((p ^ n : ℕ) : ℤ)).toAddMonoidHom

/-- The level map sends the class of `β` with `pⁿ β = f l` to the class of `l`. -/
theorem orbitRelQuotientTateLevel_eq {n : ℕ}
    (x : TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) n)
    {β : E} (hx : (x : AddAction.orbitRel.Quotient (range f) E) = Quotient.mk _ β) {l : Λ}
    (hl : f l = ((p ^ n : ℕ) : ℤ) • β) :
    f.orbitRelQuotientTateLevel hf p n x = Submodule.Quotient.mk l := by
  change Submodule.quotEquivOfEq _ _ (span_singleton_pow_smul_top_eq p n).symm
    (f.orbitRelQuotientTorsionByδ hf ((p ^ n : ℕ) : ℤ) x) = _
  rw [f.orbitRelQuotientTorsionByδ_eq hf _ x hx hl]
  rfl

/-- Every point of `T[pⁿ]` is the class of some `β` with `pⁿ β = f l`. -/
theorem exists_eq_mk_of_mem_tateModuleLevel {n : ℕ}
    (x : TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) n) :
    ∃ β : E, ∃ l : Λ, (x : AddAction.orbitRel.Quotient (range f) E) = Quotient.mk _ β ∧
      f l = ((p ^ n : ℕ) : ℤ) • β := by
  obtain ⟨β, hβ⟩ := Quotient.exists_rep (x : AddAction.orbitRel.Quotient (range f) E)
  have hx := (Submodule.mem_torsionBy_iff _ _).1 x.property
  rw [← hβ] at hx
  have h := map_zsmul (range f).orbitRelQuotientMkHom ((p ^ n : ℕ) : ℤ) β
  rw [Submodule.coe_orbitRelQuotientMkHom] at h
  rw [← h, Submodule.orbitRelQuotient_mk_eq_zero_iff] at hx
  obtain ⟨l, hl⟩ := hx
  exact ⟨β, l, hβ.symm, hl⟩

/-- **Compatibility with the transition maps.** Multiplication by `p` on `T[pⁿ⁺¹] → T[pⁿ]`
corresponds to reduction `Λ ⧸ (p)ⁿ⁺¹Λ → Λ ⧸ (p)ⁿΛ`. -/
theorem orbitRelQuotientTateLevel_transition (n : ℕ)
    (x : TateModuleLevel p (AddAction.orbitRel.Quotient (range f) E) (n + 1)) :
    f.orbitRelQuotientTateLevel hf p n
        (tateModuleTransition p (AddAction.orbitRel.Quotient (range f) E) n x) =
      factorPow (Ideal.span {(p : ℤ)}) Λ n.le_succ
        (f.orbitRelQuotientTateLevel hf p (n + 1) x) := by
  obtain ⟨β, l, hβ, hl⟩ := f.exists_eq_mk_of_mem_tateModuleLevel p x
  rw [f.orbitRelQuotientTateLevel_eq hf p x hβ hl]
  refine f.orbitRelQuotientTateLevel_eq hf p _ (β := p • β) ?_ ?_
  · rw [tateModuleTransition_apply, hβ]
    simpa [Submodule.coe_orbitRelQuotientMkHom] using
      (map_nsmul (range f).orbitRelQuotientMkHom p β).symm
  · change f l = _
    rw [hl, pow_succ, Nat.cast_mul, mul_smul]
    exact congrArg _ (natCast_zsmul β p)

/-- When multiplication by `p` is bijective on `E`, so is multiplication by `pⁿ`. -/
theorem bijective_pow_smul (hp : Bijective fun v : E ↦ (p : ℤ) • v) (n : ℕ) :
    Bijective fun v : E ↦ ((p ^ n : ℕ) : ℤ) • v := by
  have h : (fun v : E ↦ ((p ^ n : ℕ) : ℤ) • v) = (fun v : E ↦ (p : ℤ) • v)^[n] := by
    induction n with
    | zero => funext v; simp
    | succ n ih =>
      rw [Function.iterate_succ', ← ih]
      funext v
      change ((p ^ (n + 1) : ℕ) : ℤ) • v = (p : ℤ) • (((p ^ n : ℕ) : ℤ) • v)
      rw [← mul_smul, pow_succ', Nat.cast_mul]
  rw [h]
  exact hp.iterate n

/-- When multiplication by `p` is bijective on `E`, each level map `T[pⁿ] → Λ ⧸ (p)ⁿΛ` is
bijective. -/
theorem bijective_orbitRelQuotientTateLevel (hp : Bijective fun v : E ↦ (p : ℤ) • v) (n : ℕ) :
    Bijective (f.orbitRelQuotientTateLevel hf p n) := by
  have hn := bijective_pow_smul p hp n
  have h : Bijective (f.orbitRelQuotientTorsionByδ hf ((p ^ n : ℕ) : ℤ)) := by
    refine ⟨f.injective_orbitRelQuotientTorsionByδ hf _ hn.1, fun q ↦ ?_⟩
    -- lift `q = [l]` to the class of `β` with `pⁿ β = f l`
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨β, hβ⟩ := hn.2 (f l)
    have hmem : (Quotient.mk _ β : AddAction.orbitRel.Quotient (range f) E) ∈
        torsionBy ℤ (AddAction.orbitRel.Quotient (range f) E) ((p ^ n : ℕ) : ℤ) := by
      have h := map_zsmul (range f).orbitRelQuotientMkHom ((p ^ n : ℕ) : ℤ) β
      rw [Submodule.coe_orbitRelQuotientMkHom] at h
      rw [mem_torsionBy_iff, ← h, Submodule.orbitRelQuotient_mk_eq_zero_iff]
      exact ⟨l, hβ.symm⟩
    exact ⟨⟨_, hmem⟩, f.orbitRelQuotientTorsionByδ_eq hf _ ⟨_, hmem⟩ rfl hβ.symm⟩
  exact (Submodule.quotEquivOfEq _ _ (span_singleton_pow_smul_top_eq p n).symm).bijective.comp h

/-- The map from the `p`-adic Tate module of `T = E / f(Λ)` to the `p`-adic completion of `Λ`,
assembled from the level maps. -/
def tateModuleOrbitRelQuotientHom :
    TateModule p (AddAction.orbitRel.Quotient (range f) E) →+
      AdicCompletion (Ideal.span {(p : ℤ)}) Λ where
  toFun x := ⟨fun n ↦ f.orbitRelQuotientTateLevel hf p n (TateModule.proj n x), fun {m n} hmn ↦
    (Submodule.eq_factor_of_eq_factor_succ
      (fun _ _ h ↦ pow_smul_top_le _ Λ h :
        Antitone fun n ↦ (Ideal.span {(p : ℤ)} ^ n • ⊤ : Submodule ℤ Λ))
      (fun n ↦ f.orbitRelQuotientTateLevel hf p n (TateModule.proj n x))
      (fun k ↦ by rw [← TateModule.proj_succ, orbitRelQuotientTateLevel_transition]) hmn).symm⟩
  map_zero' := by ext n; simp
  map_add' x y := by
    ext n
    simp only [map_add]
    rfl

theorem tateModuleOrbitRelQuotientHom_apply_val
    (x : TateModule p (AddAction.orbitRel.Quotient (range f) E)) (n : ℕ) :
    (f.tateModuleOrbitRelQuotientHom hf p x).val n =
      f.orbitRelQuotientTateLevel hf p n (TateModule.proj n x) :=
  (rfl)

/-- When multiplication by `p` is bijective on `E`, the map from the Tate module of the torus to
the `p`-adic completion of `Λ` is bijective. -/
theorem bijective_tateModuleOrbitRelQuotientHom (hp : Bijective fun v : E ↦ (p : ℤ) • v) :
    Bijective (f.tateModuleOrbitRelQuotientHom hf p) := by
  have hb := f.bijective_orbitRelQuotientTateLevel hf p hp
  refine ⟨fun x y hxy ↦ TateModule.ext fun n ↦ (hb n).1 ?_, fun c ↦ ?_⟩
  · exact congrArg (fun z : AdicCompletion _ Λ ↦ z.val n) hxy
  · choose g hg using fun n ↦ (hb n).2 (c.val n)
    refine ⟨TateModule.mk g fun n ↦ (hb n).1 ?_, AdicCompletion.ext fun n ↦ ?_⟩
    · rw [orbitRelQuotientTateLevel_transition, hg, hg]
      exact c.property n.le_succ
    · rw [tateModuleOrbitRelQuotientHom_apply_val, TateModule.proj_mk, hg]

/-- **The Tate module of a torus.** When multiplication by `p` is bijective on `E`, the `p`-adic
Tate module of `T = E / f(Λ)` is the `p`-adic completion `lim Λ ⧸ pⁿΛ` of `Λ`: a compatible family
of torsion points `[βₙ]` with `pⁿ βₙ = f lₙ` goes to the family of classes of the `lₙ`. -/
def tateModuleOrbitRelQuotientEquiv (hp : Bijective fun v : E ↦ (p : ℤ) • v) :
    TateModule p (AddAction.orbitRel.Quotient (range f) E) ≃+
      AdicCompletion (Ideal.span {(p : ℤ)}) Λ :=
  AddEquiv.ofBijective (f.tateModuleOrbitRelQuotientHom hf p)
    (f.bijective_tateModuleOrbitRelQuotientHom hf p hp)

/-- The `n`-th component of the image of a Tate-module point whose `n`-th level is the class of
`β`, with `pⁿ β = f l`, is the class of `l`. -/
theorem tateModuleOrbitRelQuotientEquiv_apply_val (hp : Bijective fun v : E ↦ (p : ℤ) • v)
    (x : TateModule p (AddAction.orbitRel.Quotient (range f) E)) {n : ℕ} {β : E}
    (hx : (TateModule.proj n x : AddAction.orbitRel.Quotient (range f) E) = Quotient.mk _ β)
    {l : Λ} (hl : f l = ((p ^ n : ℕ) : ℤ) • β) :
    (f.tateModuleOrbitRelQuotientEquiv hf p hp x).val n = Submodule.Quotient.mk l :=
  f.orbitRelQuotientTateLevel_eq hf p _ hx hl

section Finite

variable {L : Type} [AddCommGroup L] [Module.Finite ℤ L] (g : L →ₗ[ℤ] E) (hg : Injective g)

/-- **The Tate module of a torus as `ℤ^_p ⊗ Λ`.** For finitely generated `Λ`, with `ℤ^_p` the
`p`-adic completion of `ℤ`, through Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
def tateModuleOrbitRelQuotientEquivTensor (hp : Bijective fun v : E ↦ (p : ℤ) • v) :
    TateModule p (AddAction.orbitRel.Quotient (range g) E) ≃+
      AdicCompletion (Ideal.span {(p : ℤ)}) ℤ ⊗[ℤ] L :=
  (g.tateModuleOrbitRelQuotientEquiv hg p hp).trans
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (Ideal.span {(p : ℤ)}) L).toAddEquiv.symm

end Finite

end LinearMap
