/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantizedEnvelopingAlgebra.Hopf
public import TauCeti.QuantumGroups.UqSl2.Hopf
public import TauCeti.QuantumGroups.UqSl2.Rescale

/-!
# Rank-one `U_q(sl₂)` homomorphisms at simple root nodes

For every complex parameter `q : ℂ`, symmetrizable Cartan datum `D : CartanDatum ι X Y`, and node
`i : ι`, the elements `Eᵢ`, `Fᵢ`, `Kᵢ = K_(dᵢ hᵢ)`, and `Kᵢ⁻¹ = K_(-dᵢ hᵢ)` of
`QuantizedEnvelopingAlgebra D q` satisfy the defining relations of the rank-one quantized
enveloping algebra `UqSl2 (q ^ D.symmetrizer i)`:

* `Kᵢ Kᵢ⁻¹ = Kᵢ⁻¹ Kᵢ = 1`,
* `Kᵢ Eᵢ = qᵢ² Eᵢ Kᵢ` and `Kᵢ Fᵢ = qᵢ⁻² Fᵢ Kᵢ` (`qᵢ = q ^ dᵢ`, since `aᵢᵢ = 2`), and
* `Eᵢ Fᵢ - Fᵢ Eᵢ = (Kᵢ - Kᵢ⁻¹) / (qᵢ - qᵢ⁻¹)`.

This yields a canonical complex algebra homomorphism `fromUqSl2 D q i` for every `q : ℂ`,
compatible with the unconditional counit and with the diagonal rescaling automorphisms. At a
generic parameter `[Fact (IsGenericQuantumParameter q)]`, `fromUqSl2 D q i` upgrades to a complex
bialgebra (hence Hopf algebra) homomorphism `fromUqSl2BialgHom D q i`, allowing any
`QuantizedEnvelopingAlgebra D q`-module (and tensor products or duals thereof) to be restricted to
the `i`-th rank-one quantum `sl₂` subalgebra. Injectivity of `fromUqSl2 D q i` requires the
triangular decomposition and PBW theorem of `QuantizedEnvelopingAlgebra D q`.

## Main definitions and results

* `TauCeti.QuantizedEnvelopingAlgebra.fromUqSl2`: the canonical `ℂ`-algebra homomorphism
  `UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantizedEnvelopingAlgebra D q` at node `i : ι`.
* `TauCeti.QuantizedEnvelopingAlgebra.range_fromUqSl2`: its image is the `ℂ`-subalgebra generated
  by `{Eᵢ, Fᵢ, Kᵢ, Kᵢ⁻¹}`.
* `TauCeti.QuantizedEnvelopingAlgebra.rescale_fromUqSl2`: compatibility with `rescale` and
  `UqSl2.rescale`.
* `TauCeti.QuantizedEnvelopingAlgebra.fromUqSl2BialgHom`: the bialgebra homomorphism upgrade at a
  generic parameter, together with `comul_fromUqSl2`, `counit_fromUqSl2`, and
  `fromUqSl2_antipode`.

## References

* J. C. Jantzen, *Lectures on Quantum Groups*, Graduate Studies in Mathematics 6, Section 4.3.
* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Section 3.2.
-/

public section

namespace TauCeti

/-- A generic complex quantum parameter is nonzero, making `[Fact (q ≠ 0)]` instances on `UqSl2`
available at generic parameters. -/
instance UqSl2.instFactNeZeroOfGeneric (q : ℂ) [Fact (IsGenericQuantumParameter q)] :
    Fact (q ≠ 0) :=
  ⟨(Fact.out : IsGenericQuantumParameter q).ne_zero⟩

/-- A nonzero complex quantum parameter has nonzero natural powers, making the native Hopf
structure on `UqSl2 (q ^ n)` available to importers. -/
instance UqSl2.instFactPowNeZero (q : ℂ) (n : ℕ) [Fact (q ≠ 0)] : Fact (q ^ n ≠ 0) :=
  ⟨pow_ne_zero n Fact.out⟩

namespace QuantizedEnvelopingAlgebra

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

private noncomputable def fromUqSl2Tuple (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    UqSl2.GeneratorTuple (q ^ D.symmetrizer i) (QuantizedEnvelopingAlgebra D q) where
  e := e D q i
  f := f D q i
  k := ki D q i
  kInv := kiInv D q i
  k_mul_kInv := k_mul_k_neg (D.simpleTorus i)
  kInv_mul_k := k_neg_mul_k (D.simpleTorus i)
  k_mul_e := by
    simpa only [D.cartan_apply_self, zpow_two, sq] using ki_mul_e (D := D) (q := q) i i
  k_mul_f := by
    rw [ki_mul_f, D.cartan_apply_self, zpow_neg, zpow_two, inv_pow, sq]
  e_mul_f_sub_f_mul_e := e_mul_f_sub_f_mul_e_self i

/-- The canonical complex algebra homomorphism from `UqSl2 (q ^ D.symmetrizer i)` to
`QuantizedEnvelopingAlgebra D q` at node `i : ι`, sending `E, F, K, K⁻¹` to `Eᵢ, Fᵢ, Kᵢ, Kᵢ⁻¹`. -/
noncomputable def fromUqSl2 (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    UqSl2 (q ^ D.symmetrizer i) →ₐ[ℂ] QuantizedEnvelopingAlgebra D q :=
  UqSl2.liftEquiv.symm (fromUqSl2Tuple D q i)

section Algebra

variable {D : CartanDatum ι X Y} {q : ℂ}

/-- `fromUqSl2 D q i` sends the rank-one raising generator `E` to `Eᵢ`. -/
@[simp]
theorem fromUqSl2_e (i : ι) :
    fromUqSl2 D q i (UqSl2.e (q ^ D.symmetrizer i)) = e D q i := by
  rw [← UqSl2.liftEquiv_apply_e, fromUqSl2, Equiv.apply_symm_apply]
  rfl

/-- `fromUqSl2 D q i` sends the rank-one lowering generator `F` to `Fᵢ`. -/
@[simp]
theorem fromUqSl2_f (i : ι) :
    fromUqSl2 D q i (UqSl2.f (q ^ D.symmetrizer i)) = f D q i := by
  rw [← UqSl2.liftEquiv_apply_f, fromUqSl2, Equiv.apply_symm_apply]
  rfl

/-- `fromUqSl2 D q i` sends the rank-one weight generator `K` to `Kᵢ = K_(dᵢ hᵢ)`. -/
@[simp]
theorem fromUqSl2_k (i : ι) :
    fromUqSl2 D q i (UqSl2.k (q ^ D.symmetrizer i)) = ki D q i := by
  rw [← UqSl2.liftEquiv_apply_k, fromUqSl2, Equiv.apply_symm_apply]
  rfl

/-- `fromUqSl2 D q i` sends the rank-one inverse weight generator `K⁻¹` to `Kᵢ⁻¹ = K_(-dᵢ hᵢ)`. -/
@[simp]
theorem fromUqSl2_kInv (i : ι) :
    fromUqSl2 D q i (UqSl2.kInv (q ^ D.symmetrizer i)) = kiInv D q i := by
  rw [← UqSl2.liftEquiv_apply_kInv, fromUqSl2, Equiv.apply_symm_apply]
  rfl

/-- `fromUqSl2 D q i` maps the distinguished rank-one toral unit `kUnit` to `kUnit D q (dᵢ hᵢ)`. -/
@[simp]
theorem fromUqSl2_kUnit (i : ι) :
    Units.map (fromUqSl2 D q i : UqSl2 (q ^ D.symmetrizer i) →* QuantizedEnvelopingAlgebra D q)
        (UqSl2.kUnit (q ^ D.symmetrizer i)) =
      kUnit D q (D.simpleTorus i) := by
  ext
  simp

/-- `fromUqSl2 D q i` maps rank-one divided powers of `E` to `Eᵢ^(n)`. -/
theorem fromUqSl2_quantumDividedPower_e (i : ι) (n : ℕ) :
    fromUqSl2 D q i
        (quantumDividedPower (q ^ D.symmetrizer i) (UqSl2.e (q ^ D.symmetrizer i)) n) =
      eDividedPower D q i n := by
  simp [eDividedPower]

/-- `fromUqSl2 D q i` maps rank-one divided powers of `F` to `Fᵢ^(n)`. -/
theorem fromUqSl2_quantumDividedPower_f (i : ι) (n : ℕ) :
    fromUqSl2 D q i
        (quantumDividedPower (q ^ D.symmetrizer i) (UqSl2.f (q ^ D.symmetrizer i)) n) =
      fDividedPower D q i n := by
  simp [fDividedPower]

/-- The image of `fromUqSl2 D q i` is the complex subalgebra generated by `Eᵢ, Fᵢ, Kᵢ, Kᵢ⁻¹`. -/
theorem range_fromUqSl2 (D : CartanDatum ι X Y) (q : ℂ) (i : ι) :
    (fromUqSl2 D q i).range = Algebra.adjoin ℂ {e D q i, f D q i, ki D q i, kiInv D q i} := by
  rw [← Algebra.map_top, ← UqSl2.adjoin_range_generator, AlgHom.map_adjoin]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨g, rfl⟩
    cases g <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨.e, fromUqSl2_e i⟩
    · exact ⟨.f, fromUqSl2_f i⟩
    · exact ⟨.k, fromUqSl2_k i⟩
    · exact ⟨.kInv, fromUqSl2_kInv i⟩

/-- Diagonal rescaling on `QuantizedEnvelopingAlgebra D q` restricts along `fromUqSl2 D q i` to the
rank-one rescaling automorphism `UqSl2.rescale` with parameter `c i`. -/
@[simp]
theorem rescale_fromUqSl2 (c : ι → ℂˣ) (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    rescale D q c (fromUqSl2 D q i x) =
      fromUqSl2 D q i (UqSl2.rescale (q ^ D.symmetrizer i) (c i) x) := by
  have h :
      (rescale D q c).toAlgHom.comp (fromUqSl2 D q i) =
        (fromUqSl2 D q i).comp (UqSl2.rescale (q ^ D.symmetrizer i) (c i)).toAlgHom := by
    apply UqSl2.hom_ext <;> simp
  exact AlgHom.congr_fun h x

/-- `fromUqSl2 D q i` intertwines the unconditional augmentations for every parameter `q : ℂ`. -/
theorem counit_apply_fromUqSl2 (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    counit D q (fromUqSl2 D q i x) = UqSl2.counit (q ^ D.symmetrizer i) x := by
  have h : (counit D q).comp (fromUqSl2 D q i) = UqSl2.counit (q ^ D.symmetrizer i) := by
    apply UqSl2.hom_ext <;> simp
  exact AlgHom.congr_fun h x

/-- For any nonzero parameter `q`, `fromUqSl2 D q i` intertwines the presentation-level antipode
`antipodeAlgHom` with the Hopf antipode of `UqSl2 (q ^ D.symmetrizer i)`. -/
theorem antipodeAlgHom_fromUqSl2 [Fact (q ≠ 0)] (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    antipodeAlgHom D (Fact.out : q ≠ 0) (fromUqSl2 D q i x) =
      MulOpposite.op (fromUqSl2 D q i (HopfAlgebra.antipode ℂ x)) := by
  have h :
      (antipodeAlgHom D (Fact.out : q ≠ 0)).comp (fromUqSl2 D q i) =
        (AlgHom.op (fromUqSl2 D q i)).comp (UqSl2.antipodeOp (q ^ D.symmetrizer i)) := by
    apply UqSl2.hom_ext <;> simp
  simpa using AlgHom.congr_fun h x

end Algebra

section Generic

variable (D : CartanDatum ι X Y) (q : ℂ) [Fact (IsGenericQuantumParameter q)]

/-- At a generic parameter, `fromUqSl2 D q i` upgrades to a complex bialgebra homomorphism from
`UqSl2 (q ^ D.symmetrizer i)` to `QuantizedEnvelopingAlgebra D q`. -/
noncomputable def fromUqSl2BialgHom (i : ι) :
    UqSl2 (q ^ D.symmetrizer i) →ₐc[ℂ] QuantizedEnvelopingAlgebra D q :=
  BialgHom.ofAlgHom (fromUqSl2 D q i)
    (by apply UqSl2.hom_ext <;> simp [← counit_apply])
    (by apply UqSl2.hom_ext <;> simp [Bialgebra.comulAlgHom_apply])

variable {D q}

@[simp]
theorem fromUqSl2BialgHom_toAlgHom (i : ι) :
    (fromUqSl2BialgHom D q i).toAlgHom = fromUqSl2 D q i :=
  (rfl)

@[simp]
theorem fromUqSl2BialgHom_apply (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    fromUqSl2BialgHom D q i x = fromUqSl2 D q i x :=
  (rfl)

/-- `fromUqSl2 D q i` preserves the coalgebra counit at a generic parameter. -/
@[simp]
theorem counit_fromUqSl2 (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    Coalgebra.counit (R := ℂ) (fromUqSl2 D q i x) = Coalgebra.counit (R := ℂ) x := by
  rw [← counit_apply, counit_apply_fromUqSl2, UqSl2.counit_apply]

/-- `fromUqSl2 D q i` intertwines the coalgebra coproducts at a generic parameter. -/
theorem comul_fromUqSl2 (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    Coalgebra.comul (R := ℂ) (fromUqSl2 D q i x) =
      Algebra.TensorProduct.map (fromUqSl2 D q i) (fromUqSl2 D q i)
        (Coalgebra.comul (R := ℂ) x) := by
  have h :
      (Bialgebra.comulAlgHom ℂ (QuantizedEnvelopingAlgebra D q)).comp (fromUqSl2 D q i) =
        (Algebra.TensorProduct.map (fromUqSl2 D q i) (fromUqSl2 D q i)).comp
          (Bialgebra.comulAlgHom ℂ (UqSl2 (q ^ D.symmetrizer i))) := by
    apply UqSl2.hom_ext <;> simp [Bialgebra.comulAlgHom_apply]
  exact AlgHom.congr_fun h x

/-- `fromUqSl2 D q i` commutes with the Hopf antipode at a generic parameter. -/
@[simp]
theorem fromUqSl2_antipode (i : ι) (x : UqSl2 (q ^ D.symmetrizer i)) :
    fromUqSl2 D q i (HopfAlgebra.antipode ℂ x) =
      HopfAlgebra.antipode ℂ (fromUqSl2 D q i x) := by
  simpa only [fromUqSl2BialgHom_apply] using
    BialgHomClass.map_antipode (R := ℂ) (fromUqSl2BialgHom D q i) x

end Generic

end QuantizedEnvelopingAlgebra

end TauCeti
