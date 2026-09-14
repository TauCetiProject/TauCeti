/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Socle

/-!
# Radical layers of vertex projectives over a zigzag algebra

For a finite simple graph without isolated vertices, the vertex projective `P_i = Z e_i` has
Loewy length three.  Its first radical power is spanned by the arrows leaving `i` together with
the volume at `i`; its second radical power is the volume line; and its third radical power is
zero.  Consequently the head and socle layers are one-dimensional, while the middle layer has
dimension equal to the degree of `i`.

The powers here are defined intrinsically by the algebra radical acting on `P_i`.

## Main definitions

* `TauCeti.zigzagProjectiveRadicalPower`: the submodule `J^n P_i`.
* `TauCeti.zigzagProjectiveRadicalLayer`: the quotient `J^n P_i / J^(n+1) P_i`.

## Main results

* `TauCeti.mem_zigzagProjectiveRadicalPower_one_iff`: `J P_i` is the positive-degree part of
  `P_i`.
* `TauCeti.mem_zigzagProjectiveRadicalPower_two_iff`: `J^2 P_i` is the volume line.
* `TauCeti.zigzagProjectiveRadicalPower_three_eq_bot`: `J^3 P_i = 0`.
* `TauCeti.isSimpleModule_zigzagProjectiveRadicalLayer_zero`: the head is simple.
* `TauCeti.socle_zigzagProjective_eq_radicalPower_two`: the socle is `J² P_i`.
* `TauCeti.finrank_zigzagProjectiveRadicalLayer_zero`,
  `TauCeti.finrank_zigzagProjectiveRadicalLayer_one`, and
  `TauCeti.finrank_zigzagProjectiveRadicalLayer_two`: the dimensions `1`, `deg(i)`, and `1`.

## References

See R. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3, and
M. Ehrig and D. Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => nonisolatedZigzagQuotient k G

/-- The `n`-th radical power of the vertex projective `P_i = Z e_i`, namely `J^n P_i`. -/
noncomputable def zigzagProjectiveRadicalPower (i : V) (n : ℕ) :
    Submodule Z (zigzagProjective k G i) :=
  Ring.jacobson Z ^ n • (⊤ : Submodule Z (zigzagProjective k G i))

/-- An element of `P_i` belongs to `J^n P_i` exactly when its underlying algebra element belongs
to `J^n`. -/
theorem mem_zigzagProjectiveRadicalPower_iff (i : V) (n : ℕ)
    (x : zigzagProjective k G i) :
    x ∈ zigzagProjectiveRadicalPower k G i n ↔
      (x : Z) ∈ Ring.jacobson Z ^ n := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      exact (Ring.jacobson Z ^ n).mul_mem_right (y : Z) hr
    · exact fun _ _ hx hy ↦ (Ring.jacobson Z ^ n).add_mem hx hy
  · intro hx
    have hfix : (x : Z) * zigzagVertexIdempotent k G i = x :=
      (mem_zigzagProjective_iff k G).mp x.2
    have hmem := Submodule.smul_mem_smul hx
      (show zigzagProjectiveGenerator k G i ∈
        (⊤ : Submodule Z (zigzagProjective k G i)) from Submodule.mem_top)
    have heq : (x : Z) • zigzagProjectiveGenerator k G i = x := by
      apply Subtype.ext
      -- Expose the subtype action so the algebra fixed-point criterion applies.
      change (x : Z) * (zigzagProjectiveGenerator k G i : Z) = (x : Z)
      rw [coe_zigzagProjectiveGenerator]
      exact hfix
    exact heq ▸ hmem

@[simp]
theorem zigzagProjectiveRadicalPower_zero (i : V) :
    zigzagProjectiveRadicalPower k G i 0 = ⊤ := by
  apply top_unique
  intro x _
  rw [mem_zigzagProjectiveRadicalPower_iff, Submodule.pow_zero, Ideal.one_eq_top]
  exact (show (x : Z) ∈ (⊤ : Ideal Z) from Submodule.mem_top)

/-- The radical powers of a vertex projective form a descending filtration. -/
theorem zigzagProjectiveRadicalPower_antitone (i : V) :
    Antitone (zigzagProjectiveRadicalPower k G i) := by
  intro m n hmn x hx
  rw [mem_zigzagProjectiveRadicalPower_iff] at hx ⊢
  exact Ideal.pow_le_pow_right hmn hx

/-- The `n`-th radical layer of the vertex projective, `J^n P_i / J^(n+1) P_i`. -/
noncomputable abbrev zigzagProjectiveRadicalLayer (i : V) (n : ℕ) :=
  zigzagProjectiveRadicalPower k G i n ⧸
    (zigzagProjectiveRadicalPower k G i n.succ).submoduleOf
      (zigzagProjectiveRadicalPower k G i n)

variable {k G}

/-- The first radical power of `P_i` consists exactly of the elements whose underlying algebra
element has positive path length. -/
@[simp]
theorem mem_zigzagProjectiveRadicalPower_one_iff (hns : ∀ i : V, ∃ j, G.Adj i j)
    (i : V) (x : zigzagProjective k G i) :
    x ∈ zigzagProjectiveRadicalPower k G i 1 ↔
      (x : nonisolatedZigzagQuotient k G) ∈ zigzagPositiveSpan k G := by
  rw [mem_zigzagProjectiveRadicalPower_iff, Submodule.pow_one,
    ← restrictScalars_jacobson_nonisolatedZigzagQuotient_eq_zigzagPositiveSpan hns]
  exact Iff.rfl

/-- The second radical power of `P_i` consists exactly of the elements whose underlying algebra
element lies in the span of the volume classes. -/
@[simp]
theorem mem_zigzagProjectiveRadicalPower_two_iff (hns : ∀ i : V, ∃ j, G.Adj i j)
    (i : V) (x : zigzagProjective k G i) :
    x ∈ zigzagProjectiveRadicalPower k G i 2 ↔
      (x : nonisolatedZigzagQuotient k G) ∈ zigzagVolumeSpan k G := by
  rw [mem_zigzagProjectiveRadicalPower_iff,
    ← restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan hns]
  exact Iff.rfl

/-- The third radical power of every vertex projective vanishes. -/
theorem zigzagProjectiveRadicalPower_three_eq_bot (hns : ∀ i : V, ∃ j, G.Adj i j)
    (i : V) : zigzagProjectiveRadicalPower k G i 3 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [mem_zigzagProjectiveRadicalPower_iff,
    jacobson_pow_three_nonisolatedZigzagQuotient_eq_bot hns] at hx
  exact Subtype.ext hx

variable (k G)

/-- The volume vector in the vertex projective `P_i`. -/
noncomputable def zigzagProjectiveVolume (i : V) : zigzagProjective k G i :=
  zigzagProjectiveBasisFun k G i (.inr (.inr ()))

@[simp]
theorem coe_zigzagProjectiveVolume (i : V) :
    (zigzagProjectiveVolume k G i : nonisolatedZigzagQuotient k G) =
      zigzagVolume k G i := by
  rw [zigzagProjectiveVolume, coe_zigzagProjectiveBasisFun_inr_inr]

/-- The head-coordinate map on `P_i`. It reads the coefficient of `e_i`, equivalently the value
at `i` of the vertex-coefficient homomorphism of the zigzag algebra. -/
noncomputable def zigzagProjectiveHeadCoeff (i : V) : zigzagProjective k G i →ₗ[k] k :=
  (LinearMap.proj (vertex G i)).comp <|
    (zigzagTrivialCoeff k G).toLinearMap.comp
      ((zigzagProjective k G i).restrictScalars k).subtype

@[simp]
theorem zigzagProjectiveHeadCoeff_apply (i : V) (x : zigzagProjective k G i) :
    zigzagProjectiveHeadCoeff k G i x =
      zigzagTrivialCoeff k G (x : nonisolatedZigzagQuotient k G) (vertex G i) :=
  (rfl)

@[simp]
theorem zigzagProjectiveHeadCoeff_generator (i : V) :
    zigzagProjectiveHeadCoeff k G i (zigzagProjectiveGenerator k G i) = 1 := by
  classical
  rw [zigzagProjectiveHeadCoeff_apply, coe_zigzagProjectiveGenerator,
    zigzagTrivialCoeff_vertexIdempotent]
  simp

/-- The head-coordinate map is onto. -/
theorem zigzagProjectiveHeadCoeff_surjective (i : V) :
    Function.Surjective (zigzagProjectiveHeadCoeff k G i) := by
  intro c
  refine ⟨c • zigzagProjectiveGenerator k G i, ?_⟩
  rw [map_smul, zigzagProjectiveHeadCoeff_generator, smul_eq_mul, mul_one]

/-- The one-dimensional volume line inside `P_i`. -/
noncomputable def zigzagProjectiveVolumeLine (i : V) :
    Submodule k (zigzagProjective k G i) :=
  k ∙ zigzagProjectiveVolume k G i

variable {k G}

private theorem mul_zigzagVertexIdempotent_mem_span_singleton_of_mem_zigzagVolumeSpan
    (i : V) {x : nonisolatedZigzagQuotient k G} (hx : x ∈ zigzagVolumeSpan k G) :
    x * zigzagVertexIdempotent k G i ∈ k ∙ zigzagVolume k G i := by
  rw [zigzagVolumeSpan_eq_span] at hx
  refine Submodule.span_induction (p := fun x _ ↦
    x * zigzagVertexIdempotent k G i ∈ k ∙ zigzagVolume k G i) ?_ (by simp) ?_ ?_ hx
  · rintro _ ⟨j, rfl⟩
    rcases eq_or_ne j i with rfl | hji
    · rw [zigzagVolume_mul_zigzagMk_vertexIdempotent]
      exact Submodule.mem_span_singleton_self _
    · rw [show zigzagVolume k G j * zigzagVertexIdempotent k G i = 0 by
          simpa only [zigzagVertexIdempotent] using
            zigzagVolume_mul_zigzagMk_vertexIdempotent_of_ne k G hji.symm]
      exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simpa only [add_mul] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa only [smul_mul_assoc] using Submodule.smul_mem _ c hx

/-- The second radical power of `P_i`, after restriction to the coefficient field, is exactly
the line spanned by its volume vector. -/
theorem restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    (zigzagProjectiveRadicalPower k G i 2).restrictScalars k =
      zigzagProjectiveVolumeLine k G i := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem, mem_zigzagProjectiveRadicalPower_two_iff hns] at hx
    have hfix : (x : nonisolatedZigzagQuotient k G) * zigzagVertexIdempotent k G i = x :=
      (mem_zigzagProjective_iff k G).mp x.2
    have hm := mul_zigzagVertexIdempotent_mem_span_singleton_of_mem_zigzagVolumeSpan i hx
    rw [hfix] at hm
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    rw [zigzagProjectiveVolumeLine, Submodule.mem_span_singleton]
    refine ⟨c, Subtype.ext ?_⟩
    let val : zigzagProjective k G i →ₗ[k] nonisolatedZigzagQuotient k G :=
      (zigzagProjective k G i).restrictScalars k |>.subtype
    calc
      val (c • zigzagProjectiveVolume k G i) = c • val (zigzagProjectiveVolume k G i) :=
        val.map_smul c _
      _ = c • zigzagVolume k G i := by rw [show val (zigzagProjectiveVolume k G i) =
          zigzagVolume k G i from coe_zigzagProjectiveVolume k G i]
      _ = val x := hc
  · intro x hx
    rw [zigzagProjectiveVolumeLine, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [Submodule.restrictScalars_mem, mem_zigzagProjectiveRadicalPower_two_iff hns]
    let val : zigzagProjective k G i →ₗ[k] nonisolatedZigzagQuotient k G :=
      (zigzagProjective k G i).restrictScalars k |>.subtype
    have hm := (zigzagVolumeSpan k G).smul_mem c (zigzagVolume_mem_zigzagVolumeSpan i)
    rw [show ((c • zigzagProjectiveVolume k G i : zigzagProjective k G i) :
        nonisolatedZigzagQuotient k G) = c • zigzagVolume k G i by
      calc
        ((c • zigzagProjectiveVolume k G i : zigzagProjective k G i) :
            nonisolatedZigzagQuotient k G) = val (c • zigzagProjectiveVolume k G i) := rfl
        _ = c • val (zigzagProjectiveVolume k G i) := val.map_smul c _
        _ = c • zigzagVolume k G i := by rw [show val (zigzagProjectiveVolume k G i) =
            zigzagVolume k G i from coe_zigzagProjectiveVolume k G i]]
    exact hm

/-! ### The first radical power and the head coordinate -/

/-- The kernel of the head-coordinate map is the first radical power of `P_i`. -/
theorem ker_zigzagProjectiveHeadCoeff_eq_restrictScalars_radicalPower_one
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    LinearMap.ker (zigzagProjectiveHeadCoeff k G i) =
      (zigzagProjectiveRadicalPower k G i 1).restrictScalars k := by
  ext x
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem,
    mem_zigzagProjectiveRadicalPower_one_iff hns]
  constructor
  · intro hx
    rw [mem_zigzagPositiveSpan_iff hns]
    intro j
    rw [← zigzagTrivialCoeff_apply_eq_repr hns]
    have hfix : (x : nonisolatedZigzagQuotient k G) * zigzagVertexIdempotent k G i = x :=
      (mem_zigzagProjective_iff k G).mp x.2
    have hcoeff := congrArg (fun f ↦ f (vertex G j))
      (congrArg (zigzagTrivialCoeff k G) hfix)
    rw [map_mul, Pi.mul_apply] at hcoeff
    classical
    rw [zigzagTrivialCoeff_vertexIdempotent] at hcoeff
    rcases eq_or_ne j i with rfl | hji
    · exact hx
    · simpa only [ite_eq_right hji.symm, mul_zero] using hcoeff.symm
  · intro hx
    rw [zigzagProjectiveHeadCoeff_apply]
    rw [← ker_zigzagTrivialCoeff_eq_zigzagPositiveSpan hns] at hx
    have hzero : zigzagTrivialCoeff k G (x : nonisolatedZigzagQuotient k G) = 0 := by
      have hx' : (x : nonisolatedZigzagQuotient k G) ∈
          RingHom.ker (zigzagTrivialCoeff k G).toRingHom := hx
      exact RingHom.mem_ker.mp hx'
    rw [hzero, Pi.zero_apply]

section Finite

variable [Fintype V] [DecidableRel G.Adj]

/-- The first radical power of `P_i` has dimension `deg(i) + 1`: its basis consists of the
outgoing arrows and the volume vector. -/
theorem finrank_restrictScalars_zigzagProjectiveRadicalPower_one
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.finrank k (zigzagProjectiveRadicalPower k G i 1) = G.degree i + 1 := by
  -- The restricted submodule has the same carrier; expose it to rewrite by the kernel theorem.
  change Module.finrank k ((zigzagProjectiveRadicalPower k G i 1).restrictScalars k) =
    G.degree i + 1
  let f := zigzagProjectiveHeadCoeff k G i
  have hf : f ≠ 0 := by
    intro h
    have hgen := congrArg (fun g ↦ g (zigzagProjectiveGenerator k G i)) h
    rw [zigzagProjectiveHeadCoeff_generator, LinearMap.zero_apply] at hgen
    exact one_ne_zero hgen
  let _ : Module.Finite k (zigzagProjective k G i) :=
    Module.Finite.of_basis (zigzagProjectiveBasis k G hns i)
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [ker_zigzagProjectiveHeadCoeff_eq_restrictScalars_radicalPower_one hns,
    finrank_zigzagProjective k G hns i] at hdim
  omega

end Finite

/-- The second radical power of `P_i` is one-dimensional. -/
theorem finrank_restrictScalars_zigzagProjectiveRadicalPower_two
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.finrank k (zigzagProjectiveRadicalPower k G i 2) = 1 := by
  -- The restricted submodule has the same carrier; expose it to use the volume-line theorem.
  change Module.finrank k ((zigzagProjectiveRadicalPower k G i 2).restrictScalars k) = 1
  rw [restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine hns,
    zigzagProjectiveVolumeLine, finrank_span_singleton]
  intro hzero
  have hcoe := congrArg (fun x : zigzagProjective k G i ↦
    (x : nonisolatedZigzagQuotient k G)) hzero
  rw [coe_zigzagProjectiveVolume, Submodule.coe_zero] at hcoe
  obtain ⟨j, hij⟩ := hns i
  exact zigzagVolume_ne_zero k G hij hcoe

/-- The second radical power of `P_i` is a simple module over the zigzag algebra. -/
theorem isSimpleModule_zigzagProjectiveRadicalPower_two
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    IsSimpleModule (nonisolatedZigzagQuotient k G)
      (zigzagProjectiveRadicalPower k G i 2) := by
  exact (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one
      (finrank_restrictScalars_zigzagProjectiveRadicalPower_two hns i)

/-- The socle of `P_i` is its second radical power, the simple line spanned by the volume at
`i`. -/
theorem socle_zigzagProjective_eq_radicalPower_two
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    socle (nonisolatedZigzagQuotient k G) (zigzagProjective k G i) =
      zigzagProjectiveRadicalPower k G i 2 := by
  apply le_antisymm
  · refine socle_le fun m hm x hx ↦ ?_
    rw [mem_zigzagProjectiveRadicalPower_two_iff hns]
    let inc : zigzagProjective k G i →ₗ[nonisolatedZigzagQuotient k G]
        nonisolatedZigzagQuotient k G := (zigzagProjective k G i).subtype
    let e := Submodule.equivMapOfInjective inc Subtype.val_injective m
    have hmap : IsSimpleModule (nonisolatedZigzagQuotient k G) (m.map inc) :=
      e.isSimpleModule_iff.mp hm
    have himage : (x : nonisolatedZigzagQuotient k G) ∈ m.map inc :=
      ⟨x, hx, rfl⟩
    have hsocle : (x : nonisolatedZigzagQuotient k G) ∈
        socle (nonisolatedZigzagQuotient k G) (nonisolatedZigzagQuotient k G) :=
      le_socle hmap himage
    rw [socle_nonisolatedZigzagQuotient_eq_jacobson_sq hns] at hsocle
    have hsocle' : (x : nonisolatedZigzagQuotient k G) ∈
        (Ring.jacobson (nonisolatedZigzagQuotient k G) ^ 2).restrictScalars k := hsocle
    rw [restrictScalars_jacobson_sq_nonisolatedZigzagQuotient_eq_zigzagVolumeSpan hns]
      at hsocle'
    exact hsocle'
  · intro x hx
    exact le_socle (isSimpleModule_zigzagProjectiveRadicalPower_two hns i) hx

/-- Every radical power from the third onward has dimension zero. -/
theorem finrank_restrictScalars_zigzagProjectiveRadicalPower_of_three_le
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) {n : ℕ} (hn : 3 ≤ n) :
    Module.finrank k (zigzagProjectiveRadicalPower k G i n) = 0 := by
  have hle := zigzagProjectiveRadicalPower_antitone k G i hn
  rw [zigzagProjectiveRadicalPower_three_eq_bot hns] at hle
  have hbot : zigzagProjectiveRadicalPower k G i n = ⊥ := bot_unique hle
  rw [hbot]
  exact Module.finrank_zero_of_subsingleton

/-! ### Dimensions of the radical layers -/

section Layers

/-- Rank-nullity for consecutive radical powers: the dimension of `J^n P_i / J^(n+1) P_i`
plus the dimension of the lower power is the dimension of the upper power. -/
theorem finrank_zigzagProjectiveRadicalLayer_add_finrank_succ
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) (n : ℕ) :
    Module.finrank k (zigzagProjectiveRadicalLayer k G i n) +
        Module.finrank k (zigzagProjectiveRadicalPower k G i n.succ) =
      Module.finrank k (zigzagProjectiveRadicalPower k G i n) := by
  classical
  let _ := Fintype.ofFinite V
  let _ : Module.Finite k (zigzagProjective k G i) :=
    Module.Finite.of_basis (zigzagProjectiveBasis k G hns i)
  let Pn := zigzagProjectiveRadicalPower k G i n
  let Pnext := zigzagProjectiveRadicalPower k G i n.succ
  have hle : Pnext ≤ Pn := by
    intro x hx
    exact zigzagProjectiveRadicalPower_antitone k G i n.le_succ hx
  let Pnk := Pn.restrictScalars k
  let Pnextk := Pnext.restrictScalars k
  have hlek : Pnextk ≤ Pnk := hle
  have hdim := (Pnextk.submoduleOf Pnk).finrank_quotient_add_finrank
  have hsub : Module.finrank k (Pnextk.submoduleOf Pnk) = Module.finrank k Pnextk :=
    LinearEquiv.finrank_eq (Submodule.submoduleOfEquivOfLe hlek)
  rw [hsub] at hdim
  exact hdim

/-- The head layer `P_i / J P_i` is one-dimensional. -/
theorem finrank_zigzagProjectiveRadicalLayer_zero
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.finrank k (zigzagProjectiveRadicalLayer k G i 0) = 1 := by
  classical
  let _ := Fintype.ofFinite V
  have hdim := finrank_zigzagProjectiveRadicalLayer_add_finrank_succ
    (k := k) (G := G) hns i 0
  have hzero : Module.finrank k (zigzagProjectiveRadicalPower k G i 0) = 2 + G.degree i := by
    rw [zigzagProjectiveRadicalPower_zero]
    have htop : Module.finrank k
        (↥(⊤ : Submodule (nonisolatedZigzagQuotient k G) (zigzagProjective k G i))) =
        Module.finrank k (zigzagProjective k G i) :=
      ((Submodule.topEquiv :
        (⊤ : Submodule (nonisolatedZigzagQuotient k G) (zigzagProjective k G i)) ≃ₗ[
          nonisolatedZigzagQuotient k G] zigzagProjective k G i).restrictScalars k).finrank_eq
    rw [htop, finrank_zigzagProjective k G hns i]
  rw [finrank_restrictScalars_zigzagProjectiveRadicalPower_one hns, hzero] at hdim
  omega

/-- The head `P_i / J P_i` is a simple module over the zigzag algebra. Its one-dimensional
coefficient-field structure forces every nonzero vector to generate it already under scalars. -/
theorem isSimpleModule_zigzagProjectiveRadicalLayer_zero
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    IsSimpleModule (nonisolatedZigzagQuotient k G)
      (zigzagProjectiveRadicalLayer k G i 0) := by
  exact (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one
      (finrank_zigzagProjectiveRadicalLayer_zero hns i)

/-- The middle radical layer `J P_i / J² P_i` has one dimension for each edge incident to `i`. -/
theorem finrank_zigzagProjectiveRadicalLayer_one
    [Fintype V] [DecidableRel G.Adj]
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.finrank k (zigzagProjectiveRadicalLayer k G i 1) = G.degree i := by
  have hdim := finrank_zigzagProjectiveRadicalLayer_add_finrank_succ
    (k := k) (G := G) hns i 1
  rw [finrank_restrictScalars_zigzagProjectiveRadicalPower_two hns,
    finrank_restrictScalars_zigzagProjectiveRadicalPower_one hns] at hdim
  omega

/-- The socle layer `J² P_i / J³ P_i` is one-dimensional. -/
theorem finrank_zigzagProjectiveRadicalLayer_two
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    Module.finrank k (zigzagProjectiveRadicalLayer k G i 2) = 1 := by
  classical
  have hdim := finrank_zigzagProjectiveRadicalLayer_add_finrank_succ
    (k := k) (G := G) hns i 2
  rw [finrank_restrictScalars_zigzagProjectiveRadicalPower_of_three_le hns i (by omega),
    finrank_restrictScalars_zigzagProjectiveRadicalPower_two hns, add_zero] at hdim
  exact hdim

end Layers

end TauCeti
