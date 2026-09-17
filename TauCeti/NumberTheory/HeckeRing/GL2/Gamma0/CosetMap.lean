/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import TauCeti.NumberTheory.HeckeRing.Basic
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.DoubleCoset

/-!
# Comparing the `Γ₀(N)` and level-one double cosets

**Shimura, Propositions 3.30 and 3.31.** Since `Γ₀(N) ≤ SL₂(ℤ)` and `Δ₀(N) ≤ Δ`, sending
`Γ₀(N) α Γ₀(N)` to `SL₂(ℤ) α SL₂(ℤ)` is well defined on double cosets:

```lean
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2)
```

and it is **injective on the cosets whose determinant is coprime to the level**
(`toLevelOneCoset_injOn`). Injectivity is the content: two `Γ₀(N)`-double cosets
with the same level-one double coset are recovered from it by intersecting with `Δ₀(N)`, which
is exactly `doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0_map`.

This is the injectivity step towards a later good-prime comparison of `R(Γ₀(N), Δ₀(N))` with
the level-one Hecke ring. Neither surjectivity nor compatibility with the Hecke-ring operations
is proved here: this file compares the two *coset types* only.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Props.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>), the `cosetMap`
and `shimura_prop_3_31` section. The bespoke `Delta0_inclusion` there is `Submonoid.inclusion`
here, and AINTLIB's `HeckePair` bundle is Mathlib's `HeckeCoset`.

## Main definitions

* `HeckeRing.GL2.CoprimeDetCoset`: coprimality of the determinant to a modulus, on a
  `Γ₀(N)`-double coset — at the level `N` the same condition as `CoprimeDet` — well defined
  because the coefficients have determinant one, so the determinant is constant on a coset.
* `HeckeRing.GL2.toLevelOneCoset`: the map `Γ₀(N) α Γ₀(N) ↦ SL₂(ℤ) α SL₂(ℤ)`, the `Γ₀`
  specialisation of `HeckeCoset.map`.

## Main results

* `HeckeRing.GL2.toLevelOneCoset_mk`, `HeckeRing.GL2.coprimeDetCoset_mk`,
  `HeckeRing.GL2.coprimeDetCoset_self_mk`: the computation rules on a representative.
* `HeckeRing.GL2.toLevelOneCoset_injOn`: **Shimura, Proposition 3.31** — `toLevelOneCoset` is
  injective on the set of coprime-determinant double cosets.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Propositions 3.30 and 3.31.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- **Shimura, Proposition 3.30.** Passing from a `Γ₀(N)`-double coset to the level-one double
coset of the same element, as the `HeckeCoset.map` of the three inclusions `Δ₀(N) ≤ Δ`,
`Γ₀(N) ≤ SL₂(ℤ)` (twice). -/
noncomputable def toLevelOneCoset :
    HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) →
      HeckeCoset (posDetInt 2) (SLnZ 2) (SLnZ 2) :=
  HeckeCoset.map (Delta0_le_posDetInt N) (Gamma0_map_le_SLnZ N)
    (Gamma0_map_le_SLnZ N)

/-- The computation rule for `toLevelOneCoset`: it keeps the representative and forgets the
level. -/
@[simp] lemma toLevelOneCoset_mk (g : Delta0 N) :
    toLevelOneCoset N (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) g) =
      HeckeCoset.mk (SLnZ 2) (SLnZ 2) (Submonoid.inclusion (Delta0_le_posDetInt N) g) :=
  HeckeCoset.map_mk _ _ _ g

/-- The integral matrices of two elements of one `Γ₀(N)`-double coset have equal determinant:
`Γ₀(N) ≤ SL₂(ℤ)`, and the determinant is constant on an `SL₂(ℤ)`-double coset. -/
private lemma intMatrix_det_eq_of_mem_doubleCoset {a b : GL (Fin 2) ℚ}
    (hb : b ∈ DoubleCoset.doubleCoset a ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)))
    {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : (↑a : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hB : (↑b : Matrix (Fin 2) (Fin 2) ℚ) = B.map (Int.cast : ℤ → ℚ)) : B.det = A.det := by
  have hdet := det_eq_of_mem_doubleCoset_of_le_SLnZ 2 (Gamma0_map_le_SLnZ N)
    (Gamma0_map_le_SLnZ N) hb
  have hcast : ((B.det : ℤ) : ℚ) = ((A.det : ℤ) : ℚ) := by
    rw [Int.cast_det B, Int.cast_det A, ← hB, ← hA]; exact hdet
  exact_mod_cast hcast

/-- Coprimality of the determinant to a modulus `M` depends only on the double coset. -/
private lemma gcd_det_eq_one_congr (M : ℕ) {a b : Delta0 N}
    (h : HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) a =
      HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) b) :
    (∀ A : Matrix (Fin 2) (Fin 2) ℤ,
        (↑(a : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
          Int.gcd A.det M = 1) ↔
      ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
        (↑(b : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
          Int.gcd A.det M = 1 := by
  obtain ⟨Aa, hAa, -, -, -⟩ := (mem_Delta0_iff N).mp a.2
  obtain ⟨Ab, hAb, -, -, -⟩ := (mem_Delta0_iff N).mp b.2
  have hba : Ab.det = Aa.det := intMatrix_det_eq_of_mem_doubleCoset N
    (HeckeCoset.eq_iff.mp h ▸ DoubleCoset.mem_doubleCoset_self _ _ _) hAa hAb
  -- the integral witness is unique, so each side is a statement about its single witness
  have key : ∀ {g : GL (Fin 2) ℚ} {W : Matrix (Fin 2) (Fin 2) ℤ},
      (g : Matrix (Fin 2) (Fin 2) ℚ) = W.map (Int.cast : ℤ → ℚ) →
        ((∀ A : Matrix (Fin 2) (Fin 2) ℤ,
          (g : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) → Int.gcd A.det M = 1) ↔
            Int.gcd W.det M = 1) := fun hW ↦
    ⟨fun h ↦ h _ hW, fun h A hA ↦
      (Matrix.map_injective Int.cast_injective (hA.symm.trans hW)) ▸ h⟩
  rw [key hAa, key hAb, hba]

/-- Coprimality of the determinant to a modulus `M`, as a predicate on `Γ₀(N)`-double cosets.
At `M = N` it is `CoprimeDet` on a representative. -/
def CoprimeDetCoset (M : ℕ) : HeckeCoset (Delta0 N) ((Gamma0 N).map (mapGL ℚ))
      ((Gamma0 N).map (mapGL ℚ)) → Prop :=
  Quotient.lift (fun g : Delta0 N ↦ ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
      (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
        Int.gcd A.det M = 1)
    (fun _ _ hab ↦ propext (gcd_det_eq_one_congr N M (Quotient.sound hab)))

/-- `CoprimeDetCoset` reads the determinant of any integral witness of a representative. -/
@[simp] lemma coprimeDetCoset_mk (M : ℕ) (g : Delta0 N) :
    CoprimeDetCoset N M
        (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) g) ↔
      ∀ A : Matrix (Fin 2) (Fin 2) ℤ,
        (↑(g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ) →
          Int.gcd A.det M = 1 :=
  Iff.rfl

/-- At the level itself, `CoprimeDetCoset` is `CoprimeDet` on any representative.

Not a `simp` lemma: `coprimeDetCoset_mk` already rewrites the left-hand side, so this
specialisation is stated off the simp normal form. -/
lemma coprimeDetCoset_self_mk (g : Delta0 N) :
    CoprimeDetCoset N N
        (HeckeCoset.mk ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) g) ↔
      CoprimeDet N g := by
  obtain ⟨A, hA, -, -, -⟩ := (mem_Delta0_iff N).mp g.2
  rw [coprimeDetCoset_mk, coprimeDet_iff N hA]
  exact ⟨fun h ↦ h A hA, fun h A' hA' ↦
    (Matrix.map_injective Int.cast_injective (hA'.symm.trans hA)) ▸ h⟩

/-- **Shimura, Proposition 3.31.** `toLevelOneCoset` is injective on the double cosets whose
determinant is coprime to `N`: the level-one double coset determines the `Γ₀(N)` one, because
intersecting it with `Δ₀(N)` returns the latter. -/
theorem toLevelOneCoset_injOn :
    Set.InjOn (toLevelOneCoset N) {D | CoprimeDetCoset N N D} := by
  rintro D₁ hD₁ D₂ hD₂ h
  -- work with representatives, so that `toLevelOneCoset_mk` applies
  have hD₁' : CoprimeDet N D₁.rep :=
    (coprimeDetCoset_self_mk N D₁.rep).mp (by rwa [HeckeCoset.mk_rep])
  have hD₂' : CoprimeDet N D₂.rep :=
    (coprimeDetCoset_self_mk N D₂.rep).mp (by rwa [HeckeCoset.mk_rep])
  rw [← HeckeCoset.mk_rep D₁, ← HeckeCoset.mk_rep D₂] at h ⊢
  rw [toLevelOneCoset_mk, toLevelOneCoset_mk, HeckeCoset.eq_iff, Submonoid.coe_inclusion,
    Submonoid.coe_inclusion] at h
  obtain ⟨Aa, hAa, -, -, -⟩ := (mem_Delta0_iff N).mp D₁.rep.2
  obtain ⟨Ab, hAb, -, -, -⟩ := (mem_Delta0_iff N).mp D₂.rep.2
  refine HeckeCoset.eq_iff.mpr ?_
  -- each `Γ₀(N)`-double coset is its level-one one cut down to `Δ₀(N)`, and those agree
  rw [← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0_map N _ D₁.rep.2 Aa hAa
      ((coprimeDet_iff N hAa).mp hD₁'),
    ← doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0_map N _ D₂.rep.2 Ab hAb
      ((coprimeDet_iff N hAb).mp hD₂'), h]

end HeckeRing.GL2
