/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.LocalNorm

/-!
# Principal ideles that are idele norms

For an extension `L/K` of number fields, the main result,
`unitEmbedding_mem_range_ideleNormMap_iff`, says that `x ∈ Kˣ` is a norm at every place
(`TauCeti.GlobalNumberFields.IsLocalNormEverywhere`) exactly when its principal idele is the norm
of an idele of `L`. It is the principal case of the placewise criterion
`mem_range_ideleNormMap_iff`. With the Hasse norm theorem for cyclic extensions, which identifies
global norms with principal ideles that are idele norms, it turns the Hasse norm principle into a
statement about norm equations in the completions. The easy half of that principle holds for
every extension: a global norm is a norm everywhere (`isLocalNormEverywhere_normUnits`).

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2 (norms of ideles) and §4 (the Hasse norm
  theorem).
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [NumberField K] [NumberField L]

/-- **Principal idele norms are local norms everywhere.** For an extension `L/K` of number fields,
the principal idele of `x ∈ Kˣ` is the norm of an idele of `L` exactly when `x` is a norm from the
local étale algebra `K_v ⊗[K] L` at every finite and every infinite place `v` of `K`. -/
theorem unitEmbedding_mem_range_ideleNormMap_iff (x : Kˣ) :
    IdeleGroup.unitEmbedding (𝓞 K) K x ∈ (ideleNormMap K L).toMonoidHom.range ↔
      IsLocalNormEverywhere K L x := by
  simp only [mem_range_ideleNormMap_iff, HeightOneSpectrum.ideleFiniteCoord_unitEmbedding,
    InfinitePlace.ideleInfiniteCoord_unitEmbedding, IsLocalNormEverywhere, IsFiniteLocalNorm,
    IsInfiniteLocalNorm]

/-- **A global norm is a local norm everywhere.** This is the easy half of the Hasse norm
principle, valid for every extension of number fields. -/
theorem isLocalNormEverywhere_normUnits (y : Lˣ) :
    IsLocalNormEverywhere K L (Algebra.normUnits K y) :=
  (unitEmbedding_mem_range_ideleNormMap_iff _).mp
    ⟨IdeleGroup.unitEmbedding (𝓞 L) L y, ideleNormMap_unitEmbedding K L y⟩

end TauCeti.GlobalNumberFields
