/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basis
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Basic
import TauCeti.NumberTheory.Padics.InverseLimit

/-!
# The prescription property as prescribed values of crossed homomorphisms

Let `G` be a pro-`p` group, `χ : G →ₜ* ℤ_pˣ` a continuous character and `I(χ)/pⁱ = ZModTwist χ i`
the twisted coefficients `ℤ/pⁱ` with `g` acting by `χ(g)`. Labute's prescription property of `χ`
(`TauCeti.HasPrescriptionProperty`) asks that every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` be
surjective. This file proves its third formulation (Labute, Prop. 6, condition (iii)): for a
topologically finitely generated pro-`p` group and a minimal generating tuple `g₁, …, gₙ`, the
property holds exactly when every tuple `c₁, …, cₙ` of `p`-adic integers is the tuple of values of
a compatible system of continuous crossed homomorphisms `fᵢ : G → I(χ)/pⁱ`, `fᵢ(gⱼ) = cⱼ mod pⁱ`.
Such a compatible system is the same thing as a continuous crossed homomorphism `F : G → ℤ_p`,
`F(xy) = χ(x) F(y) + F(x)`, with values `F(gⱼ) = cⱼ`, since `ℤ_p` is the inverse limit of the
`ℤ/pⁱ`; both forms are proved, and the second is the one downstream applications read: it converts
Kummer-compatible finite-level data into prescribed values `F(gⱼ)` of a continuous crossed
homomorphism `F : G → ℤ_p` for `χ`.

The bottom level `I(χ)/p` is special: a pro-`p` group acts trivially on it, because a continuous
character of a pro-`p` group takes values in the principal units `1 + pℤ_p`
(`TauCeti.IsProP.charScalar_one_eq_one`), so the continuous `1`-cocycles with values in `I(χ)/p` are
the continuous homomorphisms `G → 𝔽_p`. These are determined by their values on a topological
generating set, and take any prescribed values on a family that is linearly independent in the
Frattini quotient (`TauCeti.IsTopologicallyFinitelyGenerated.exists_continuousMonoidHom_apply_eq`).
This is why the hypotheses of the two directions differ: the construction of a compatible system
with prescribed values needs linear independence of the Frattini classes of `g`, while the converse
needs only that `g` generates `G` topologically.

## Main results

* `TauCeti.HasPrescriptionProperty.exists_forall_reduce_eq_and_val_eq`: under the prescription
  property, every tuple `c : ι → ℤ_p` is realized on a family `g` with linearly independent
  Frattini classes by a compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`.
* `TauCeti.hasPrescriptionProperty_of_forall_exists_forall_reduce_eq_and_val_eq`: conversely, if
  every tuple is so realized on a topological generating family, the character has the
  prescription property.
* `TauCeti.IsProP.hasPrescriptionProperty_iff_forall_exists_forall_reduce_eq_and_val_eq`: the
  equivalence, for the lifts of a basis of the Frattini quotient, that is for a minimal generating
  tuple.
* `TauCeti.exists_continuous_forall_mul_eq_and_forall_toZModPow_eq_val` and
  `TauCeti.exists_forall_reduce_eq_and_forall_val_eq_toZModPow`: a compatible system of continuous
  `1`-cocycles with values in the `I(χ)/pⁱ` is the family of reductions of a continuous crossed
  homomorphism `G → ℤ_p`, and conversely.
* `TauCeti.IsProP.hasPrescriptionProperty_iff_forall_exists_continuous_forall_mul_eq_and_apply_eq`:
  the prescription property is the existence, for every tuple `c`, of a continuous crossed
  homomorphism `F : G → ℤ_p` for `χ` with `F(gⱼ) = cⱼ` on a minimal generating tuple.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6.
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-! ### Compatible systems with prescribed values -/

section System

variable [IsTopologicalGroup G] [CompactSpace G] {χ : G →ₜ* ℤ_[p]ˣ}

variable (hχ : HasPrescriptionProperty χ) (hG : IsProP p G)
  (hfg : IsTopologicallyFinitelyGenerated G) {ι : Type*} {g : ι → G}
  (hg : LinearIndependent (ZMod p) fun k ↦
    Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)))
  (c : ι → ℤ_[p])
include hχ hG hfg hg

/-- **One step of the compatible system.** Under the prescription property, a continuous
`1`-cocycle `f : G → I(χ)/pⁱ` with values `c k mod pⁱ` on a family `g` with linearly independent
Frattini classes is the reduction of a continuous `1`-cocycle `G → I(χ)/pⁱ⁺¹` with values
`c k mod pⁱ⁺¹`. -/
theorem HasPrescriptionProperty.exists_succ_forall_reduce_eq_and_val_eq {i : ℕ}
    (f : Z1 G (ZModTwist χ i))
    (hf : ∀ k, ((f : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k)) :
    ∃ f' : Z1 G (ZModTwist χ (i + 1)),
      (∀ x, ZModTwist.reduce χ (Nat.le_succ i) ((f' : G → ZModTwist χ (i + 1)) x) =
        (f : G → ZModTwist χ i) x) ∧
      ∀ k, ((f' : G → ZModTwist χ (i + 1)) (g k)).val = PadicInt.toZModPow (i + 1) (c k) := by
  obtain ⟨f₀, hf₀⟩ := hχ.exists_forall_reduce_eq (Nat.le_succ i) f
  -- the values on the generators are corrected by `pⁱ` times a homomorphism into `I(χ)/p`
  have h1 : 1 + i = i + 1 := Nat.add_comm 1 i
  have hδ (k : ι) : ∃ ε : ZModTwist χ 1, ZModTwist.mulPow χ h1 ε =
      ⟨PadicInt.toZModPow (i + 1) (c k)⟩ - (f₀ : G → ZModTwist χ (i + 1)) (g k) := by
    obtain ⟨ε, hε⟩ := (ZModTwist.shortExact χ h1).exists_incl_eq
      (b := ⟨PadicInt.toZModPow (i + 1) (c k)⟩ - (f₀ : G → ZModTwist χ (i + 1)) (g k)) (by
        rw [ZModTwist.shortExact_proj_apply, map_sub, hf₀, ZModTwist.ext_iff, ZModTwist.val_sub,
          ZModTwist.val_reduce, ZMod.castHom_apply, PadicInt.cast_toZModPow _ _ (Nat.le_succ i),
          hf, sub_self, ZModTwist.val_zero])
    rw [ZModTwist.shortExact_incl_apply] at hε
    exact ⟨ε, hε⟩
  choose ε hε using hδ
  -- `I(χ)/p` is an `𝔽_p`-vector space, so a continuous `𝔽_p`-character takes the values `ε`
  let : Module (ZMod p) (ZModTwist χ 1) := AddCommGroup.zmodModule fun x ↦
    (ZModTwist.equiv χ 1).injective (by
      rw [map_nsmul, map_zero, ZModTwist.equiv_apply, nsmul_eq_mul,
        (CharP.cast_eq_zero_iff (ZMod (p ^ 1)) (p ^ 1) p).mpr (by rw [pow_one]), zero_mul])
  obtain ⟨ψ, hψ⟩ := hfg.exists_continuousMonoidHom_apply_eq hg ε
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : Z1 G (ZModTwist χ 1),
      ∀ x, (h₁ : G → ZModTwist χ 1) x = Multiplicative.toAdd (ψ x) :=
    ⟨(Z1EquivOfSmulEqSelf (hG.smul_zModTwist_one_eq_self χ)).symm (Additive.ofMul ψ), fun x ↦ by
      rw [Z1EquivOfSmulEqSelf_symm_apply, toMul_ofMul]⟩
  obtain ⟨h', hh'⟩ : ∃ h' : Z1 G (ZModTwist χ (i + 1)), ∀ x,
      (h' : G → ZModTwist χ (i + 1)) x = ZModTwist.mulPow χ h1 ((h₁ : G → ZModTwist χ 1) x) :=
    ⟨cocyclesMap1 G (ZModTwist χ 1) G (ZModTwist χ (i + 1)) (ContinuousMonoidHom.id G)
      (ZModTwist.mulPow χ h1) continuous_of_discreteTopology
      (fun g m ↦ (ZModTwist.mulPow χ h1).map_smul g m) h₁,
      fun x ↦ cocyclesMap1_apply G _ G _ (ContinuousMonoidHom.id G) _
        continuous_of_discreteTopology (fun g m ↦ (ZModTwist.mulPow χ h1).map_smul g m) h₁ x⟩
  refine ⟨f₀ + h', fun x ↦ ?_, fun k ↦ ?_⟩
  · rw [AddSubgroup.coe_add, Pi.add_apply, map_add, hf₀, hh', ZModTwist.reduce_mulPow, add_zero]
  · rw [AddSubgroup.coe_add, Pi.add_apply, hh', hh₁, hψ, toAdd_ofAdd, hε, add_sub_cancel]

/-- **The prescription property gives compatible systems of crossed homomorphisms with
prescribed values** (Labute, Prop. 6, (i) ⇒ (iii)). Let `G` be a topologically finitely generated
pro-`p` group, `χ` a continuous character with the prescription property and `g : ι → G` a family
whose classes in the Frattini quotient are linearly independent over `𝔽_p`. Then for every
`c : ι → ℤ_p` there are continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`, compatible under the reductions
`I(χ)/pⁱ → I(χ)/pʲ`, with `fᵢ (g k) = c k mod pⁱ` for every `i` and `k`. -/
theorem HasPrescriptionProperty.exists_forall_reduce_eq_and_val_eq :
    ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (k : ι), ((f i : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k) := by
  -- the admissible cocycles at each level, and the step between consecutive levels
  let S : ℕ → Type u := fun i ↦
    {f : Z1 G (ZModTwist χ i) //
      ∀ k, ((f : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k)}
  have hstep : ∀ (i : ℕ) (f : S i), ∃ f' : S (i + 1), ∀ x,
      ZModTwist.reduce χ (Nat.le_succ i) ((f'.1 : G → ZModTwist χ (i + 1)) x) =
        (f.1 : G → ZModTwist χ i) x := fun i f ↦ by
    obtain ⟨f', hf'₁, hf'₂⟩ := hχ.exists_succ_forall_reduce_eq_and_val_eq hG hfg hg c f.1 f.2
    exact ⟨⟨f', hf'₂⟩, hf'₁⟩
  choose step hstep using hstep
  have h0 : S 0 := ⟨0, fun k ↦
    have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.2 (pow_zero p)
    Subsingleton.elim _ _⟩
  let seq : ∀ i, S i := fun i ↦ Nat.rec h0 step i
  refine ⟨fun i ↦ (seq i).1, fun i j h x ↦ ?_, fun i k ↦ (seq i).2 k⟩
  induction i, h using Nat.le_induction with
  | base => exact ZModTwist.reduce_self χ _
  | succ i hji ih =>
    calc ZModTwist.reduce χ (hji.trans (Nat.le_succ i))
          (((seq (i + 1)).1 : G → ZModTwist χ (i + 1)) x)
        = ZModTwist.reduce χ hji (ZModTwist.reduce χ (Nat.le_succ i)
            (((seq (i + 1)).1 : G → ZModTwist χ (i + 1)) x)) :=
          (ZModTwist.reduce_reduce χ (Nat.le_succ i) hji _).symm
      _ = ((seq j).1 : G → ZModTwist χ j) x := by rw [hstep i (seq i) x, ih]

end System

/-! ### Prescribed values give the prescription property -/

section Converse

variable [IsTopologicalGroup G] {χ : G →ₜ* ℤ_[p]ˣ} {ι : Type*} {g : ι → G}
  (hg : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤)
include hg

/-- **Compatible systems with prescribed values give the prescription property** (Labute,
Prop. 6, (iii) ⇒ (i)). If `g` generates `G` topologically and every `c : ι → ℤ_p` is the tuple of
values on `g` of a compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`, then `χ` has the
prescription property. No pro-`p` or finite-generation hypothesis on `G` is needed. -/
theorem hasPrescriptionProperty_of_forall_exists_forall_reduce_eq_and_val_eq
    (h : ∀ c : ι → ℤ_[p], ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (k : ι), ((f i : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k)) :
    HasPrescriptionProperty χ := by
  refine (hasPrescriptionProperty_iff χ).2 fun i hi y ↦ ?_
  induction y using QuotientAddGroup.induction_on with
  | _ f₁ =>
  choose c hc using fun k ↦
    ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) 1) ((f₁ : G → ZModTwist χ 1) (g k)).val
  obtain ⟨f, hf, hfc⟩ := h c
  have h1 : (f 1 : G → ZModTwist χ 1) = f₁ :=
    eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top (f 1).2 f₁.2 hg (by
      rintro _ ⟨k, rfl⟩
      exact ZModTwist.ext ((hfc 1 k).trans (hc k)))
  refine ⟨f i, ?_⟩
  rw [explicitCoeff1_mk]
  refine congrArg _ (Subtype.ext (funext fun x ↦ ?_))
  rw [← congrFun h1 x, ← hf hi x]
  exact cocyclesMap1_apply G _ G _ (ContinuousMonoidHom.id G) _ continuous_of_discreteTopology
    (fun g m ↦ (ZModTwist.reduce χ hi).map_smul g m) (f i) x

end Converse

/-- **Labute's third formulation of the prescription property** (Labute, Prop. 6, (i) ⇔ (iii)).
Let `G` be a topologically finitely generated pro-`p` group and `g : ι → G` a minimal generating
tuple, that is a family of lifts of a basis `b` of the Frattini quotient over `𝔽_p`. A continuous
character `χ` has the prescription property exactly when every `c : ι → ℤ_p` is the tuple of values
on `g` of a compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ`. -/
theorem IsProP.hasPrescriptionProperty_iff_forall_exists_forall_reduce_eq_and_val_eq
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) {ι : Type*}
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G))) {g : ι → G}
    (hgb : ∀ k, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)) = b k)
    (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ c : ι → ℤ_[p], ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (k : ι), ((f i : G → ZModTwist χ i) (g k)).val = PadicInt.toZModPow i (c k) :=
  ⟨fun hχ c ↦ hχ.exists_forall_reduce_eq_and_val_eq hG hfg
    (by simpa only [hgb] using b.linearIndependent) c,
    hasPrescriptionProperty_of_forall_exists_forall_reduce_eq_and_val_eq
      (topologicallyGenerates_of_basis_frattiniQuotient hG b g hgb)⟩

/-! ### Crossed homomorphisms with values in `ℤ_p`

A compatible system of continuous `1`-cocycles `fᵢ : G → I(χ)/pⁱ` is the family of reductions of a
single continuous map `F : G → ℤ_p` satisfying the crossed-homomorphism identity
`F (x * y) = χ x * F y + F x` for the action of `G` on `ℤ_p` through `χ`, and conversely. The
identity is written out rather than expressed through a module structure on `ℤ_p`, which would
install a second action on a Mathlib type. -/

section PadicInt

variable {χ : G →ₜ* ℤ_[p]ˣ}

/-- **A compatible system of crossed homomorphisms assembles into a `p`-adic one.** Continuous
`1`-cocycles `fᵢ : G → I(χ)/pⁱ` compatible under the reductions are the reductions modulo `pⁱ` of a
continuous map `F : G → ℤ_p` with `F (x * y) = χ x * F y + F x`. -/
theorem exists_continuous_forall_mul_eq_and_forall_toZModPow_eq_val
    (f : ∀ i : ℕ, Z1 G (ZModTwist χ i))
    (hf : ∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
      ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) :
    ∃ F : G → ℤ_[p], Continuous F ∧ (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧
      ∀ (i : ℕ) (x : G), PadicInt.toZModPow i (F x) = ((f i : G → ZModTwist χ i) x).val := by
  -- the residue family of `x`
  let r : G → PadicInt.inverseLimit p := fun x ↦
    ⟨fun i ↦ ((f i : G → ZModTwist χ i) x).val, PadicInt.mem_inverseLimit_iff.mpr fun m n hmn ↦ by
      have h := congrArg ZModTwist.val (hf hmn x)
      rwa [ZModTwist.val_reduce, ZMod.castHom_apply] at h⟩
  have hr (i : ℕ) (x : G) :
      PadicInt.toZModPow i (PadicInt.fromInverseLimit p (r x)) =
        ((f i : G → ZModTwist χ i) x).val := by
    have h := RingHom.congr_fun (PadicInt.toZModPow_fromInverseLimit p i) (r x)
    rwa [RingHom.comp_apply, PadicInt.inverseLimit.proj_apply] at h
  refine ⟨fun x ↦ PadicInt.fromInverseLimit p (r x), ?_, fun x y ↦ ?_, hr⟩
  · -- `fromInverseLimit` is the inverse of the homeomorphism `inverseLimitHomeomorph`, whose
    -- underlying equivalence is `inverseLimitRingEquiv`
    have hcont : Continuous (PadicInt.fromInverseLimit p) :=
      (PadicInt.inverseLimitHomeomorph p).symm.continuous.congr fun y ↦
        (congrArg (fun e : ℤ_[p] ≃ PadicInt.inverseLimit p ↦ e.symm y)
          (PadicInt.inverseLimitHomeomorph_toEquiv p)).trans
          (PadicInt.inverseLimitRingEquiv_symm_apply p y)
    exact hcont.comp ((continuous_pi fun i ↦
      continuous_of_discreteTopology.comp (mem_Z1_iff.1 (f i).2).1).subtype_mk _)
  · refine PadicInt.ext_of_toZModPow.1 fun i ↦ ?_
    have h := congrArg ZModTwist.val ((mem_Z1_iff.1 (f i).2).2 x y)
    rw [ZModTwist.val_add, ZModTwist.val_smul, charScalar_apply] at h
    rw [map_add, map_mul, hr, hr, hr, h]

/-- **A `p`-adic crossed homomorphism reduces to a compatible system.** A continuous `F : G → ℤ_p`
with `F (x * y) = χ x * F y + F x` reduces modulo the `pⁱ` to continuous `1`-cocycles
`fᵢ : G → I(χ)/pⁱ`, compatible under the reductions, with `fᵢ x = F x mod pⁱ`. -/
theorem exists_forall_reduce_eq_and_forall_val_eq_toZModPow (F : G → ℤ_[p]) (hFc : Continuous F)
    (hF : ∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) :
    ∃ f : ∀ i : ℕ, Z1 G (ZModTwist χ i),
      (∀ ⦃i j : ℕ⦄ (h : j ≤ i) (x : G),
        ZModTwist.reduce χ h ((f i : G → ZModTwist χ i) x) = (f j : G → ZModTwist χ j) x) ∧
      ∀ (i : ℕ) (x : G), ((f i : G → ZModTwist χ i) x).val = PadicInt.toZModPow i (F x) := by
  refine ⟨fun i ↦ ⟨fun x ↦ ⟨PadicInt.toZModPow i (F x)⟩, mem_Z1_iff.2 ⟨?_, fun x y ↦ ?_⟩⟩,
    fun i j hji x ↦ ?_, fun i x ↦ rfl⟩
  · exact (continuous_of_discreteTopology (f := fun t : ZMod (p ^ i) ↦
      (⟨t⟩ : ZModTwist χ i))).comp ((PadicInt.continuous_toZModPow i).comp hFc)
  · exact ZModTwist.ext (by
      simp only [ZModTwist.val_add, ZModTwist.val_smul, charScalar_apply, hF, map_add, map_mul])
  · exact ZModTwist.ext (by
      simp only [ZModTwist.val_reduce, ZMod.castHom_apply, PadicInt.cast_toZModPow _ _ hji])

variable [IsTopologicalGroup G] [CompactSpace G] {ι : Type*} {g : ι → G}

/-- **The prescription property gives `p`-adic crossed homomorphisms with prescribed values.**
Let `G` be a topologically finitely generated pro-`p` group, `χ` a continuous character with the
prescription property and `g : ι → G` a family whose classes in the Frattini quotient are linearly
independent over `𝔽_p`. Then for every `c : ι → ℤ_p` there is a continuous `F : G → ℤ_p` with
`F (x * y) = χ x * F y + F x` and `F (g k) = c k`. -/
theorem HasPrescriptionProperty.exists_continuous_forall_mul_eq_and_apply_eq
    (hχ : HasPrescriptionProperty χ) (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
    (hg : LinearIndependent (ZMod p) fun k ↦
      Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)))
    (c : ι → ℤ_[p]) :
    ∃ F : G → ℤ_[p], Continuous F ∧ (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧
      ∀ k, F (g k) = c k := by
  obtain ⟨f, hf, hfc⟩ := hχ.exists_forall_reduce_eq_and_val_eq hG hfg hg c
  obtain ⟨F, hFc, hFmul, hF⟩ := exists_continuous_forall_mul_eq_and_forall_toZModPow_eq_val f hf
  exact ⟨F, hFc, hFmul, fun k ↦ PadicInt.ext_of_toZModPow.1 fun i ↦ (hF i (g k)).trans (hfc i k)⟩

omit [CompactSpace G] in
/-- **`p`-adic crossed homomorphisms with prescribed values give the prescription property.** If `g`
generates `G` topologically and every `c : ι → ℤ_p` is the tuple of values on `g` of a continuous
`F : G → ℤ_p` with `F (x * y) = χ x * F y + F x`, then `χ` has the prescription property. No pro-`p`
or finite-generation hypothesis on `G` is needed. -/
theorem hasPrescriptionProperty_of_forall_exists_continuous_forall_mul_eq_and_apply_eq
    (hg : (Subgroup.closure (Set.range g)).topologicalClosure = ⊤)
    (h : ∀ c : ι → ℤ_[p], ∃ F : G → ℤ_[p], Continuous F ∧
      (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧ ∀ k, F (g k) = c k) :
    HasPrescriptionProperty χ := by
  refine hasPrescriptionProperty_of_forall_exists_forall_reduce_eq_and_val_eq hg fun c ↦ ?_
  obtain ⟨F, hFc, hFmul, hF⟩ := h c
  obtain ⟨f, hf, hfF⟩ := exists_forall_reduce_eq_and_forall_val_eq_toZModPow F hFc hFmul
  exact ⟨f, hf, fun i k ↦ (hfF i (g k)).trans (congrArg (PadicInt.toZModPow i) (hF k))⟩

/-- **Labute's third formulation of the prescription property, `p`-adic form** (Labute, Prop. 6,
(i) ⇔ (iii)). Let `G` be a topologically finitely generated pro-`p` group and `g : ι → G` a minimal
generating tuple, that is a family of lifts of a basis `b` of the Frattini quotient over `𝔽_p`. A
continuous character `χ` has the prescription property exactly when every `c : ι → ℤ_p` is the tuple
of values on `g` of a continuous crossed homomorphism `F : G → ℤ_p` for `χ`, that is a continuous
`F` with `F (x * y) = χ x * F y + F x`. -/
theorem IsProP.hasPrescriptionProperty_iff_forall_exists_continuous_forall_mul_eq_and_apply_eq
    [TotallyDisconnectedSpace G] (hG : IsProP p G) (hfg : IsTopologicallyFinitelyGenerated G)
    (b : Module.Basis ι (ZMod p) (Additive (G ⧸ proPFrattini p G)))
    (hgb : ∀ k, Additive.ofMul ((QuotientGroup.mk' (proPFrattini p G)) (g k)) = b k)
    (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ ∀ c : ι → ℤ_[p], ∃ F : G → ℤ_[p], Continuous F ∧
      (∀ x y, F (x * y) = (χ x : ℤ_[p]) * F y + F x) ∧ ∀ k, F (g k) = c k :=
  ⟨fun hχ c ↦ hχ.exists_continuous_forall_mul_eq_and_apply_eq hG hfg
    (by simpa only [hgb] using b.linearIndependent) c,
    hasPrescriptionProperty_of_forall_exists_continuous_forall_mul_eq_and_apply_eq
      (topologicallyGenerates_of_basis_frattiniQuotient hG b g hgb)⟩

end PadicInt

end TauCeti
